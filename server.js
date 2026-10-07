'use strict';
/* ============================================================
   SNAKE.IO — servidor multiplayer (salas)
   - O servidor roda a partida (movimento, colisão, comida, IAs).
   - Os navegadores só mandam a direção/turbo e desenham o que recebem.
   - Cada sala aceita até 30 jogadores; se faltar gente, o servidor
     preenche com IAs (e tira as IAs quando entram mais jogadores).
   ============================================================ */
const http = require('http');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 8080;
// Opcional: só aceita conexões vindas do seu site. Ex.: https://seuusuario.github.io
const ALLOWED_ORIGIN = process.env.ALLOWED_ORIGIN || '';

const TICK_MS = 50;                 // 20 atualizações por segundo
const DT = TICK_MS / 1000;
const SEG = 2, SPEED = 46, BOOST_MULT = 1.9, TURN = 3.7, TURN_BOOST = 2.5;
const START_MASS = 12, NPM = 1.5, MAX_NODES = 420;
const BOOST_COST = 1;               // turbo gasta ~1 de tamanho por segundo (antes 15)
const BOOST_DROP = 0.5;             // a cada quantos segundos o turbo solta uma bolinha
const SPAWN_PROTECT = 3;            // segundos de proteção ao nascer (jogadores)
const MAX_ROOMS = 30;
const MAX_PLAYERS = 30;             // limite de jogadores por sala
const TARGET_POP = 16;              // jogadores + IAs por sala (as IAs preenchem o que faltar)
const ARENA_R = 1000;

/* ---------------- utilidades ---------------- */
function nodesFor(m){ return Math.max(10, Math.min(MAX_NODES, Math.round(m * NPM))); }
function radiusFor(m){ return Math.min(9, 3 + Math.floor(Math.sqrt(Math.max(0, m - 12)) / 2.4)); }
/* path[0] é SEMPRE a cabeça exata; os nós seguintes ficam a SEG de distância (corpo contínuo) */
function syncBody(s){
  const p = s.path;
  if(p.length === 0) p.push({ x: s.x, y: s.y });
  if(p.length === 1) p.push({ x: s.x - Math.cos(s.angle) * SEG, y: s.y - Math.sin(s.angle) * SEG });
  p[0].x = s.x; p[0].y = s.y;
  let guard = 0;
  while(guard++ < 40){
    const a = p[0], b = p[1];
    const dx = a.x - b.x, dy = a.y - b.y, d = Math.hypot(dx, dy);
    if(d < SEG) break;
    const k = SEG / d;
    p.splice(1, 0, { x: b.x + dx * k, y: b.y + dy * k });
  }
}
/* raio de cada nó: IGUAL ao que o cliente desenha (o rabo afina nos últimos 8 nós) */
function bodyRadiusAt(o, i, n){
  const t = n - 1 - i;
  return t < 8 ? Math.max(2, Math.round(o.r * (0.55 + 0.45 * t / 8))) : o.r;
}
function headRadius(s){ return s.boosting ? s.r + 1 : s.r; }
function bodyGap(hx, hy, hr, o){
  const p = o.path, n = p.length;
  let best = 1e9;
  for(let i = 0; i < n; i++){
    const dx = p[i].x - hx, dy = p[i].y - hy;
    const g = Math.sqrt(dx * dx + dy * dy) - hr - bodyRadiusAt(o, i, n);
    if(g < best) best = g;
  }
  return best;
}
function angleDiff(a, b){
  let d = a - b;
  while(d > Math.PI) d -= Math.PI * 2;
  while(d < -Math.PI) d += Math.PI * 2;
  return d;
}
function randPoint(maxD){
  const a = Math.random() * Math.PI * 2;
  const d = Math.sqrt(Math.random()) * maxD;
  return { x: Math.cos(a) * d, y: Math.sin(a) * d };
}
const r1 = function(v){ return Math.round(v * 10) / 10; };
const r2 = function(v){ return Math.round(v * 100) / 100; };

function cleanName(v, max){
  return String(v == null ? '' : v).toUpperCase().replace(/[^A-Z0-9 .\-]/g, '').replace(/^\s+/, '').trim().slice(0, max);
}
function cleanPass(v){
  return String(v == null ? '' : v).toUpperCase().replace(/[^A-Z0-9]/g, '').slice(0, 12);
}

/* AI-CORE-BEGIN  (mesmo código no jogo e no servidor — não editar só de um lado) */
const AI_SEG = 2;
const FOOD_CELL = 60;

/* parâmetros de cada dificuldade */
const DIFF = [
  { // FÁCIL: reage devagar, erra a mira, quase não ataca
    reactMin:0.22, reactMax:0.40, stratMin:1.2,  stratMax:2.6,
    noise:0.30, err:0.35, look:0.8,  aggr:0.12, hunt:0.70, boost:0.0, flee:0.35, turn:0.82, mistake:0.025 },
  { // MÉDIO
    reactMin:0.10, reactMax:0.18, stratMin:0.7,  stratMax:1.5,
    noise:0.14, err:0.14, look:1.0,  aggr:0.40, hunt:0.85, boost:0.5, flee:0.75, turn:0.95, mistake:0.006 },
  { // DIFÍCIL: reflexo rápido, corta a frente, foge de cobra maior
    reactMin:0.04, reactMax:0.08, stratMin:0.35, stratMax:0.8,
    noise:0.05, err:0.04, look:1.3,  aggr:0.80, hunt:1.00, boost:1.0, flee:1.0,  turn:1.0,  mistake:0 }
];

/* tamanhos variados: pequenas, médias, grandes e gigantes */
function randAiMass(initial){
  const r = Math.random();
  if(initial){
    if(r < 0.45) return 10 + Math.random() * 25;
    if(r < 0.78) return 35 + Math.random() * 65;
    if(r < 0.94) return 100 + Math.random() * 120;
    return 220 + Math.random() * 180;
  }
  if(r < 0.6) return 10 + Math.random() * 20;
  if(r < 0.9) return 30 + Math.random() * 50;
  return 80 + Math.random() * 100;
}

/* campos de IA que toda cobra controlada pela IA precisa ter */
function aiFields(angle){
  return {
    turnMul: 1, state: 'wander', prey: null, threat: null,
    err: 0, phase: Math.random() * 6.28,
    stratT: Math.random() * 0.8, steerT: Math.random() * 0.1,
    desAngle: angle, blind: 0, boostT: 0, boostCool: 0,
    skipUntil: 0, skipX: 0, skipY: 0, nearTarget: null, nearSince: 0
  };
}

/* ---------- onde nascer sem cruzar ninguém ---------- */
/* testa o corpo inteiro (para trás) e o caminho à frente contra todas as cobras vivas */
function findSpawn(w, mass, opt){
  const n = nodesFor(mass), rn = radiusFor(mass);
  const list = [];
  for(let i = 0; i < w.snakes.length; i++) if(!w.snakes[i].dead) list.push(w.snakes[i]);
  const nb = Math.ceil(n / 3);
  const total = nb + Math.ceil(opt.ahead / 10);
  const lim = (w.R - 45) * (w.R - 45);
  let best = null, bestGap = -1e9;
  for(let t = 0; t < 90; t++){
    const a0 = Math.random() * Math.PI * 2, dd = Math.sqrt(Math.random()) * opt.maxD;
    const x = Math.cos(a0) * dd, y = Math.sin(a0) * dd;
    const angle = opt.outward ? Math.atan2(y, x) + (Math.random() - 0.5) * 1.2 : Math.random() * Math.PI * 2;
    const ca = Math.cos(angle), sa = Math.sin(angle);
    let minGap = 1e9, wall = false;
    for(let i = 0; i < total && !wall; i++){
      const dist = i < nb ? -i * 3 * AI_SEG : (i - nb + 1) * 10;
      const px = x + ca * dist, py = y + sa * dist;
      if(px * px + py * py > lim){ wall = true; break; }
      for(let k = 0; k < list.length; k++){
        const o = list[k], b = o.bbox;
        const m = rn + o.r + opt.clear + 6;
        if(px < b.x0 - m || px > b.x1 + m || py < b.y0 - m || py > b.y1 + m) continue;
        let md2 = (o.x - px) * (o.x - px) + (o.y - py) * (o.y - py);
        for(let q = 0; q < o.path.length; q += 2){
          const dx = o.path[q].x - px, dy = o.path[q].y - py;
          const d2 = dx * dx + dy * dy;
          if(d2 < md2) md2 = d2;
        }
        const gap = Math.sqrt(md2) - rn - o.r;
        if(gap < minGap) minGap = gap;
      }
    }
    if(wall) continue;
    if(minGap >= opt.clear) return { x: x, y: y, angle: angle, gap: minGap };
    if(minGap > bestGap){ bestGap = minGap; best = { x: x, y: y, angle: angle, gap: minGap }; }
  }
  return best || { x: 0, y: 0, angle: Math.random() * Math.PI * 2, gap: -1 };
}

/* ---------- mapa de comida (grade) para as IAs "enxergarem" onde tem bolinha ---------- */
function foodKey(cx, cy){ return (cx + 64) * 128 + (cy + 64); }

function rebuildFoodGrid(w, list){
  const g = w.grid;
  g.clear();
  for(const f of list){
    if(f.gone) continue;
    const cx = Math.floor(f.x / FOOD_CELL), cy = Math.floor(f.y / FOOD_CELL);
    const k = foodKey(cx, cy);
    let c = g.get(k);
    if(!c){ c = { list: [], sum: 0, sx: 0, sy: 0 }; g.set(k, c); }
    c.list.push(f);
    c.sum += f.m * (f.big ? 1.6 : 1);
    c.sx += f.x; c.sy += f.y;
  }
}

function foodRichness(w, x, y, rad){
  const x0 = Math.floor((x - rad) / FOOD_CELL), x1 = Math.floor((x + rad) / FOOD_CELL);
  const y0 = Math.floor((y - rad) / FOOD_CELL), y1 = Math.floor((y + rad) / FOOD_CELL);
  let sum = 0;
  for(let cx = x0; cx <= x1; cx++){
    for(let cy = y0; cy <= y1; cy++){
      const c = w.grid.get(foodKey(cx, cy));
      if(c) sum += c.sum;
    }
  }
  return sum;
}

/* bolinha mais "gostosa" por perto (perto, grande e à frente) */
function bestFoodAround(w, s, rad){
  const rad2 = rad * rad;
  const x0 = Math.floor((s.x - rad) / FOOD_CELL), x1 = Math.floor((s.x + rad) / FOOD_CELL);
  const y0 = Math.floor((s.y - rad) / FOOD_CELL), y1 = Math.floor((s.y + rad) / FOOD_CELL);
  const skip = w.time < s.skipUntil;
  let best = null, bs = 0;
  for(let cx = x0; cx <= x1; cx++){
    for(let cy = y0; cy <= y1; cy++){
      const c = w.grid.get(foodKey(cx, cy));
      if(!c) continue;
      for(let i = 0; i < c.list.length; i++){
        const f = c.list[i];
        if(f.gone) continue;
        const dx = f.x - s.x, dy = f.y - s.y, d2 = dx * dx + dy * dy;
        if(d2 > rad2) continue;
        if(skip && Math.abs(f.x - s.skipX) < 14 && Math.abs(f.y - s.skipY) < 14) continue;
        const dist = Math.sqrt(d2);
        const ang = Math.abs(angleDiff(Math.atan2(dy, dx), s.angle));
        if(dist < 22 && ang > 1.3) continue;           // colada e atrás: pega na volta
        const sc = f.m * (f.big ? 1.8 : 1) / (dist + 10) * (1.35 - ang * 0.3);
        if(sc > bs){ bs = sc; best = f; }
      }
    }
  }
  return best;
}

/* melhor "monte" de comida mais longe (restos de cobra morta, aglomerados) */
function bestCluster(w, s, d, scary){
  const rad = (320 + s.r * 10) * d.look;
  const cr = Math.ceil(rad / FOOD_CELL);
  const ccx = Math.floor(s.x / FOOD_CELL), ccy = Math.floor(s.y / FOOD_CELL);
  let best = null, bs = 0;
  for(let cx = ccx - cr; cx <= ccx + cr; cx++){
    for(let cy = ccy - cr; cy <= ccy + cr; cy++){
      const c = w.grid.get(foodKey(cx, cy));
      if(!c || c.sum <= 0) continue;
      const n = c.list.length;
      const mx = c.sx / n, my = c.sy / n;
      const dx = mx - s.x, dy = my - s.y;
      const dist = Math.hypot(dx, dy);
      if(dist > rad) continue;
      const ang = Math.abs(angleDiff(Math.atan2(dy, dx), s.angle));
      const sc = c.sum / (dist + 45) * (1.3 - ang * 0.22);
      if(sc <= bs) continue;
      let bad = false;
      for(let j = 0; j < scary.length; j++){
        if(Math.hypot(mx - scary[j].x, my - scary[j].y) < 60 + scary[j].r * 3){ bad = true; break; }
      }
      if(bad) continue;
      bs = sc; best = { x: mx, y: my };
    }
  }
  return best;
}

/* ---------- percepção de perigo ---------- */
function obstaclePenalty(w, px, py, self){
  let minD = 1e9;
  const list = w.snakes;
  for(let k = 0; k < list.length; k++){
    const o = list[k];
    if(o === self || o.dead) continue;
    const b = o.bbox;
    const m = 36 + o.r;
    if(px < b.x0 - m || px > b.x1 + m || py < b.y0 - m || py > b.y1 + m) continue;
    let minD2 = 1e9;
    let hx = o.x - px, hy = o.y - py;
    let hd = hx * hx + hy * hy;
    if(hd < minD2) minD2 = hd;
    hx = o.x + Math.cos(o.angle) * 16 - px; hy = o.y + Math.sin(o.angle) * 16 - py;
    hd = hx * hx + hy * hy;
    if(hd < minD2) minD2 = hd;
    const step = o.path.length > 50 ? 2 : 1;
    for(let i = 0; i < o.path.length; i += step){
      const n = o.path[i];
      const dx = n.x - px, dy = n.y - py;
      const d2 = dx * dx + dy * dy;
      if(d2 < minD2) minD2 = d2;
    }
    const d = Math.sqrt(minD2) - (o.r - 3) - (self.r - 3);
    if(d < minD) minD = d;
  }
  if(minD > 18) return 0;
  return Math.min(1.5, (18 - minD) / 18);
}

function wander(w, s){
  const a = Math.random() * Math.PI * 2;
  const dist = 90 + Math.random() * 220;
  let tx = s.x + Math.cos(a) * dist;
  let ty = s.y + Math.sin(a) * dist;
  const dd = Math.hypot(tx, ty);
  const lim = w.R * 0.88;
  if(dd > lim){ tx *= lim / dd; ty *= lim / dd; }
  s.tx = tx; s.ty = ty;
}

/* decisão estratégica: fugir, caçar, comer ou passear */
function aiStrategy(w, s){
  const d = DIFF[w.diff];
  s.err = (Math.random() - 0.5) * 2 * d.err;
  s.prey = null; s.threat = null;
  const list = w.snakes;

  const scary = [];
  let threat = null, td = 1e9;
  const tr = (140 + s.r * 6) * d.look;
  for(let i = 0; i < list.length; i++){
    const o = list[i];
    if(o === s || o.dead || o.mass <= s.mass * 1.2) continue;
    const dd = Math.hypot(o.x - s.x, o.y - s.y);
    if(dd < 420) scary.push(o);
    if(dd < tr && dd < td){ td = dd; threat = o; }
  }
  if(threat && Math.random() < d.flee){
    s.state = 'flee'; s.threat = threat; return;
  }

  // com fome (muita comida por perto) a IA caça bem menos
  let aggr = d.aggr;
  if(foodRichness(w, s.x, s.y, 120) > 5) aggr *= 0.25;
  if(Math.random() < aggr){
    let bestS = 0, prey = null;
    const lim = (260 + s.r * 8) * d.look;
    for(let i = 0; i < list.length; i++){
      const o = list[i];
      if(o === s || o.dead || o.mass > s.mass * d.hunt) continue;
      const dd = Math.hypot(o.x - s.x, o.y - s.y);
      if(dd > lim) continue;
      let sc = (o.mass + 20) / (dd + 40);
      if(o.isPlayer && w.diff > 0) sc *= 1.5;
      if(sc > bestS){ bestS = sc; prey = o; }
    }
    if(prey){ s.state = 'hunt'; s.prey = prey; return; }
  }

  const cl = bestCluster(w, s, d, scary);
  if(cl){ s.state = 'food'; s.tx = cl.x; s.ty = cl.y; return; }
  s.state = 'wander'; wander(w, s);
}

/* ângulo desejado conforme o estado (com ruído "humano") */
function aiGoalAngle(w, s, d){
  let tx = s.tx, ty = s.ty;
  const st = s.state;
  if(st === 'flee'){
    const th = s.threat;
    if(!th || th.dead){ s.state = 'wander'; s.stratT = 0; }
    else {
      const dist = Math.hypot(th.x - s.x, th.y - s.y);
      if(dist > 300){ s.state = 'wander'; s.stratT = 0; }
      else {
        let ax = s.x - th.x, ay = s.y - th.y;
        const al = Math.hypot(ax, ay) || 1; ax /= al; ay /= al;
        const cl = Math.hypot(s.x, s.y) || 1;
        const wgt = Math.max(0, cl / w.R - 0.4) * 1.4;     // perto da borda, mistura com o centro
        ax += (-s.x / cl) * wgt; ay += (-s.y / cl) * wgt;
        tx = s.x + ax * 100; ty = s.y + ay * 100;
        if(dist < 100 + th.r * 3 && s.mass > 24 && s.boostCool <= 0 && Math.random() < d.boost){
          s.boostT = 0.5 + Math.random() * 0.6; s.boostCool = 2.2;
        }
      }
    }
  } else if(st === 'hunt'){
    const pr = s.prey;
    if(!pr || pr.dead){ s.state = 'wander'; s.stratT = 0; }
    else {
      const dist = Math.hypot(pr.x - s.x, pr.y - s.y);
      if(dist > 480){ s.state = 'wander'; s.stratT = 0; }
      else {
        // mira à frente da cabeça da presa para cortar o caminho
        const lead = Math.max(24, Math.min(120, dist * 0.7));
        tx = pr.x + Math.cos(pr.angle) * lead;
        ty = pr.y + Math.sin(pr.angle) * lead;
        const aimErr = Math.abs(angleDiff(Math.atan2(ty - s.y, tx - s.x), s.angle));
        if(dist > 50 && dist < 190 && aimErr < 0.5 && s.mass > 30 && s.boostCool <= 0 && Math.random() < d.boost * 0.5){
          s.boostT = 0.5 + Math.random() * 0.7; s.boostCool = 3;
        }
      }
    }
  } else {
    // comendo / passeando: vai sempre atrás da bolinha mais próxima à frente (varre o monte inteiro)
    const nf = bestFoodAround(w, s, st === 'food' ? 95 : 70);
    if(nf){
      s.state = 'food'; s.tx = nf.x; s.ty = nf.y; tx = nf.x; ty = nf.y;
      const dd = Math.hypot(nf.x - s.x, nf.y - s.y);
      if(dd < 28){
        // colada mas sem conseguir pegar (órbita): ignora essa bolinha por um tempo
        if(s.nearTarget !== nf){ s.nearTarget = nf; s.nearSince = w.time; }
        else if(w.time - s.nearSince > 1.1){ s.skipX = nf.x; s.skipY = nf.y; s.skipUntil = w.time + 4; s.nearTarget = null; }
      } else s.nearTarget = null;
    } else if(st === 'food'){
      if(Math.hypot(tx - s.x, ty - s.y) < 14) s.stratT = 0;      // chegou: escolhe o próximo monte
    } else {
      if(Math.hypot(tx - s.x, ty - s.y) < 30) wander(w, s);
    }
  }
  const sway = (st === 'hunt' || st === 'flee') ? 0.35 : 1;
  return Math.atan2(ty - s.y, tx - s.x) + s.err + Math.sin(w.time * 1.7 + s.phase) * d.noise * sway;
}

/* escolhe a melhor direção livre perto do ângulo desejado (antenas à frente) */
function aiSteer(w, s, desired, d){
  const R = s.r;
  const look1 = (16 + R * 2) * d.look;
  const look2 = look1 * 2.1;
  const wl = w.R - 28 - R;
  const blind = s.blind > 0;
  let bestScore = -1e9, bestA = s.angle;
  for(let k = -7; k <= 7; k++){
    const off = k * 0.22;
    const a = s.angle + off;
    const c = Math.cos(a), sn = Math.sin(a);
    const x1 = s.x + c * look1, y1 = s.y + sn * look1;
    const x2 = s.x + c * look2, y2 = s.y + sn * look2;
    let score = -Math.abs(angleDiff(desired, a)) * 1.6 - Math.abs(off) * 0.12;
    const b1 = Math.hypot(x1, y1), b2 = Math.hypot(x2, y2);
    if(b1 > wl) score -= 6 + (b1 - wl) * 0.5;
    if(b2 > wl) score -= 2 + (b2 - wl) * 0.15;
    if(!blind){
      score -= obstaclePenalty(w, x1, y1, s) * 10;
      score -= obstaclePenalty(w, x2, y2, s) * 4;
    }
    if(score > bestScore){ bestScore = score; bestA = a; }
  }
  return bestA;
}

function aiThink(w, s, dt){
  const d = DIFF[w.diff];
  s.stratT -= dt; s.steerT -= dt;
  if(s.blind > 0) s.blind -= dt;
  if(s.boostCool > 0) s.boostCool -= dt;
  if(s.boostT > 0) s.boostT -= dt;

  if(s.stratT <= 0){
    s.stratT = d.stratMin + Math.random() * (d.stratMax - d.stratMin);
    aiStrategy(w, s);
  }
  if(s.steerT <= 0){
    s.steerT = d.reactMin + Math.random() * (d.reactMax - d.reactMin);
    if(d.mistake && Math.random() < d.mistake) s.blind = 0.5 + Math.random() * 0.6;
    s.desAngle = aiSteer(w, s, aiGoalAngle(w, s, d), d);
  }
  // suaviza a mudança de direção (movimento fluido)
  s.targetAngle += angleDiff(s.desAngle, s.targetAngle) * Math.min(1, dt * 9);
  s.wantBoost = s.boosting = s.boostT > 0 && s.mass > 20;
}
/* AI-CORE-END */

const BOT_NAMES = ['VIPER','KOBRA','MAMBA','PITON','TAIPAN','NAJA','SUCURI','JARARA','CASCAVEL','BOA','ANACONDA','CORAL',
  'DRAGAO','FURIA','ZUMBI','JIBOIA','URUTU','BOIUNA','SERPE','VENENO','SOMBRA','RAIO','TROVAO','LOBO','TIGRE','ONCA',
  'FALCAO','NINJA','REI','HYDRA','COBRAO','VESPA','ESCAMA','FOGO','GELO','NEON','TURBO','BRUTO','GIGANTE','MINI'];

const rooms = new Map();
let nextRoomId = 1, nextClientId = 1;
let tickMsSum = 0, tickCount = 0;
const GUARD_TOTAL = { valid: 0, blocked: 0 };

function send(c, obj){
  if(c.ws.readyState === 1){
    try{ c.ws.send(typeof obj === 'string' ? obj : JSON.stringify(obj)); }catch(e){}
  }
}
function sendErr(c, msg){ send(c, { t: 'err', msg: msg }); }

/* ---------------- sala ---------------- */
class Room {
  constructor(name, pass){
    this.id = String(nextRoomId++);
    this.name = name;
    this.max = MAX_PLAYERS;
    this.pass = pass;                                   // '' = pública
    this.R = ARENA_R;
    this.foodMax = Math.round(Math.PI * this.R * this.R / 2300);
    this.clients = new Map();                           // id -> jogador
    this.snakes = new Map();                            // id -> cobra viva (jogadores e IAs)
    this.food = new Map();
    this.nextFood = 1;
    this.fa = []; this.fr = [];                         // comidas novas / removidas (deltas)
    this.host = null;
    this.w = { snakes: [], R: this.R, time: 0, diff: 1, grid: new Map() };   // "mundo" que a IA enxerga
    this.tickNo = 0; this.guard = { checked: 0, valid: 0, blocked: 0 };
    this.gridT = 0; this.botCool = 0; this.nextBot = 1; this.botName = Math.floor(Math.random() * BOT_NAMES.length);
    for(let i = 0; i < this.foodMax; i++){
      const p = randPoint(this.R * 0.96);
      this.addFood(p.x, p.y, 0.7, false);
    }
    this.fa = [];
    this.fillBots(true);
    this.timer = setInterval(() => this.tick(), TICK_MS);
  }

  addFood(x, y, m, big){
    const f = { id: this.nextFood++, x: r1(x), y: r1(y), m: r2(m), big: !!big, gone: false };
    this.food.set(f.id, f);
    this.fa.push([f.id, f.x, f.y, f.m, f.big ? 1 : 0]);
  }

  trimFood(){
    const cap = this.foodMax * 2.2;
    while(this.food.size > cap){
      const k = this.food.keys().next().value;
      const f = this.food.get(k);
      if(f) f.gone = true;
      this.food.delete(k);
      this.fr.push(k);
    }
  }

  broadcast(msg){
    for(const c of this.clients.values()) send(c, msg);
  }

  sendMeta(){
    const players = [];
    for(const c of this.clients.values()) players.push({ id: c.id, name: c.nick, c: c.id % 8 });
    for(const s of this.snakes.values()) if(s.isBot) players.push({ id: s.id, name: s.name, c: (-s.id * 3) % 8 });
    this.broadcast({ t: 'meta', players: players });
  }

  newSnake(id, name, sp, mass){
    const s = {
      id: id, name: name, x: sp.x, y: sp.y, angle: sp.angle, targetAngle: sp.angle, tx: sp.x, ty: sp.y,
      mass: mass, r: radiusFor(mass), path: [], boosting: false, wantBoost: false,
      dead: false, dropT: 0, isBot: false, isPlayer: false, protect: 0, gPend: null, gPendTick: 0,
      bbox: { x0: sp.x, y0: sp.y, x1: sp.x, y1: sp.y }
    };
    const n = nodesFor(mass);
    for(let i = 0; i < n; i++){
      const q = { x: sp.x - Math.cos(sp.angle) * i * SEG, y: sp.y - Math.sin(sp.angle) * i * SEG };
      s.path.push(q);
      if(q.x < s.bbox.x0) s.bbox.x0 = q.x; if(q.x > s.bbox.x1) s.bbox.x1 = q.x;
      if(q.y < s.bbox.y0) s.bbox.y0 = q.y; if(q.y > s.bbox.y1) s.bbox.y1 = q.y;
    }
    return s;
  }

  /* jogador humano: nasce longe de todo mundo, sem cruzar corpo nenhum */
  spawn(c, mass){
    mass = mass || START_MASS;
    this.w.snakes = Array.from(this.snakes.values());
    const sp = findSpawn(this.w, mass, { maxD: this.R * 0.6, clear: 60, ahead: 170, outward: false });
    const s = this.newSnake(c.id, c.nick, sp, mass);
    s.isPlayer = true;
    s.protect = SPAWN_PROTECT;                          // nasce protegido (pisca no cliente)
    this.snakes.set(c.id, s);
    c.snake = s;
  }

  /* ---------- IAs de preenchimento ---------- */
  botCount(){
    let n = 0;
    for(const s of this.snakes.values()) if(s.isBot) n++;
    return n;
  }

  spawnBot(initial){
    this.w.snakes = Array.from(this.snakes.values());
    let mass = randAiMass(initial), sp;
    for(let k = 0; k < 4; k++){
      sp = findSpawn(this.w, mass, { maxD: this.R * (mass > 150 ? 0.6 : 0.82), clear: 12, ahead: 50, outward: true });
      if(sp.gap >= 0 || mass < 14) break;
      mass = Math.max(10, mass * 0.7);
    }
    const id = -(this.nextBot++);
    const s = this.newSnake(id, BOT_NAMES[(this.botName++) % BOT_NAMES.length], sp, mass);
    s.isBot = true;
    Object.assign(s, aiFields(sp.angle));
    s.turnMul = DIFF[1].turn;
    this.snakes.set(id, s);
    if(!initial && this.clients.size) this.sendMeta();
  }

  fillBots(initial){
    const want = Math.max(0, TARGET_POP - this.clients.size);
    let have = this.botCount();
    if(initial){
      while(have < want){ this.spawnBot(true); have++; }
      return;
    }
    if(have > want){
      for(const s of this.snakes.values()){
        if(s.isBot){ this.kill(s, null, true); break; }       // entrou gente: uma IA sai
      }
    } else if(have < want && this.botCool <= 0){
      this.spawnBot(false);
      this.botCool = 1 + Math.random() * 1.5;
    }
  }

  move(s){
    s.boosting = s.wantBoost && s.mass > 14;
    if(s.boosting){
      s.mass -= BOOST_COST * DT;
      s.dropT += DT;
      if(s.dropT > BOOST_DROP){
        s.dropT = 0;
        const n = s.path[Math.min(s.path.length - 1, 5)];
        if(n) this.addFood(n.x + (Math.random() - 0.5) * 3, n.y + (Math.random() - 0.5) * 3, BOOST_COST * BOOST_DROP * 0.6, false);
      }
    }
    const turn = (s.boosting ? TURN_BOOST : TURN) * (s.turnMul || 1) * DT;
    const d = angleDiff(s.targetAngle, s.angle);
    s.angle += Math.max(-turn, Math.min(turn, d));
    if(s.angle > Math.PI) s.angle -= Math.PI * 2;
    else if(s.angle < -Math.PI) s.angle += Math.PI * 2;

    const spd = SPEED * (s.boosting ? BOOST_MULT : 1);
    s.x += Math.cos(s.angle) * spd * DT;
    s.y += Math.sin(s.angle) * spd * DT;

    syncBody(s);
    const maxN = nodesFor(s.mass);
    while(s.path.length > maxN) s.path.pop();
    s.r = radiusFor(s.mass);

    let x0 = s.x, y0 = s.y, x1 = s.x, y1 = s.y;
    const st = s.path.length > 60 ? 2 : 1;
    for(let i = 0; i < s.path.length; i += st){
      const n = s.path[i];
      if(n.x < x0) x0 = n.x; if(n.x > x1) x1 = n.x;
      if(n.y < y0) y0 = n.y; if(n.y > y1) y1 = n.y;
    }
    s.bbox.x0 = x0; s.bbox.y0 = y0; s.bbox.x1 = x1; s.bbox.y1 = y1;
  }

  collide(){
    const list = this.w.snakes;
    for(let a = 0; a < list.length; a++){
      const s = list[a];
      if(s.dead || s.protect > 0) continue;
      if(s.x * s.x + s.y * s.y > (this.R - 1) * (this.R - 1)){ this.tryKill(s, null); continue; }
      for(let b = 0; b < list.length; b++){
        const o = list[b];
        if(o === s || o.dead) continue;
        if(o.protect > 0) continue;                 // cobra protegida (piscando) não mata ninguém
        const bb = o.bbox;
        const mg = s.r + o.r + 4;
        if(s.x < bb.x0 - mg || s.x > bb.x1 + mg || s.y < bb.y0 - mg || s.y > bb.y1 + mg) continue;
        const hr = headRadius(s);
        const hth = hr + headRadius(o) - 2;
        const hdx = o.x - s.x, hdy = o.y - s.y;
        if(hdx * hdx + hdy * hdy < hth * hth){ this.tryKill(s, o); break; }
        let hit = false;
        const n = o.path.length, st = n > 60 ? 2 : 1;
        for(let i = 0; i < n; i += st){
          const q = o.path[i];
          const tt = hr + bodyRadiusAt(o, i, n) - 2;
          const dx = q.x - s.x, dy = q.y - s.y;
          if(dx * dx + dy * dy < tt * tt){ hit = true; break; }
        }
        if(hit){ this.tryKill(s, o); break; }
      }
    }
  }

  /* ---------- IA GUARDIÃ: analisa a morte ANTES de ela acontecer ----------
     Só vale: bater na BORDA ou na cobra de OUTRO. Nunca o próprio corpo.
     O contato precisa se confirmar em 2 ticks seguidos e passar na checagem exata. */
  verifyKill(s, killer){
    if(!isFinite(s.x) || !isFinite(s.y)) return 'POSICAO INVALIDA';
    if(s.protect > 0) return 'PROTEGIDA';
    if(!killer) return Math.hypot(s.x, s.y) > this.R - 1 ? '' : 'BORDA FALSA';
    if(killer === s) return 'PROPRIO CORPO';
    if(killer.dead) return 'ATACANTE MORTO';
    if(killer.protect > 0) return 'ATACANTE FANTASMA';
    const hr = headRadius(s);
    const hdx = killer.x - s.x, hdy = killer.y - s.y, hth = hr + headRadius(killer) - 2;
    if(hdx * hdx + hdy * hdy < hth * hth) return '';
    if(bodyGap(s.x, s.y, hr, killer) < -2) return '';
    return 'SEM CONTATO';
  }

  tryKill(s, killer){
    const key = killer ? killer.id : 'wall';
    if(s.gPend !== key || this.tickNo - s.gPendTick > 2){ s.gPend = key; s.gPendTick = this.tickNo; return false; }
    if(this.tickNo === s.gPendTick) return false;
    s.gPend = null;
    this.guard.checked++;
    const why = this.verifyKill(s, killer);
    if(why){
      this.guard.blocked++;
      GUARD_TOTAL.blocked++;
      return false;                                  // morte inválida: ninguém morre
    }
    this.guard.valid++; GUARD_TOTAL.valid++;
    this.kill(s, killer, false, true);
    return true;
  }

  kill(s, killer, silent, verified){
    if(s.dead) return;
    s.dead = true;
    this.snakes.delete(s.id);
    const total = s.mass * 0.8;
    const cnt = Math.max(4, Math.min(110, Math.floor(s.path.length / 2)));
    const per = Math.max(0.5, Math.min(6, total / cnt));
    const step = Math.max(1, Math.floor(s.path.length / cnt));
    for(let i = 0; i < s.path.length; i += step){
      const n = s.path[i];
      this.addFood(n.x + (Math.random() - 0.5) * 2, n.y + (Math.random() - 0.5) * 2, per, per > 1.6);
    }
    this.trimFood();
    const c = this.clients.get(s.id);
    if(c){
      c.snake = null;
      c.lastMass = s.mass; c.lastDeathT = Date.now();   // para renascer com o mesmo tamanho se a morte for cancelada
      if(!silent) send(c, { t: 'dead', mass: Math.round(s.mass), by: killer ? killer.name : '', v: verified ? 1 : 0 });
    }
    if(killer){
      const kc = this.clients.get(killer.id);
      if(kc) send(kc, { t: 'kill', name: s.name });
    }
  }

  eat(){
    for(const s of this.snakes.values()){
      const rr = s.r + 3.2, rr2 = rr * rr;
      for(const f of this.food.values()){
        const dx = f.x - s.x, dy = f.y - s.y;
        if(dx * dx + dy * dy < rr2){
          s.mass += f.m;
          f.gone = true;
          this.food.delete(f.id);
          this.fr.push(f.id);
        }
      }
    }
  }

  tick(){
    const t0 = Date.now();
    this.w.time += DT;
    this.tickNo++;
    this.botCool -= DT;
    this.w.snakes = Array.from(this.snakes.values());
    this.gridT -= DT;
    if(this.gridT <= 0){ this.gridT = 0.15; rebuildFoodGrid(this.w, this.food.values()); }

    for(const s of this.w.snakes) if(s.isBot) aiThink(this.w, s, DT);
    for(const s of this.w.snakes){ if(s.protect > 0) s.protect -= DT; this.move(s); }
    this.collide();
    this.eat();
    this.fillBots(false);

    if(this.food.size < this.foodMax){
      const n = Math.min(5, this.foodMax - this.food.size);
      for(let i = 0; i < n; i++){
        const p = randPoint(this.R * 0.96);
        this.addFood(p.x, p.y, 0.7, false);
      }
    }
    const p = [];
    for(const s of this.snakes.values()){
      p.push([s.id, r1(s.x), r1(s.y), r2(s.angle), r1(s.mass), s.boosting ? 1 : 0, s.protect > 0 ? 1 : 0]);
    }
    const msg = { t: 's', p: p };
    if(this.fa.length) msg.fa = this.fa;
    if(this.fr.length) msg.fr = this.fr;
    this.fa = []; this.fr = [];
    this.broadcast(JSON.stringify(msg));
    tickMsSum += Date.now() - t0; tickCount++;
  }

  destroy(){
    clearInterval(this.timer);
    rooms.delete(this.id);
  }
}

/* ---------------- entrar / sair ---------------- */
function joinRoom(c, room, nick){
  c.nick = nick;
  c.room = room;
  room.clients.set(c.id, c);
  if(!room.host) room.host = c.id;
  room.spawn(c);
  const food = [];
  for(const f of room.food.values()) food.push([f.id, f.x, f.y, f.m, f.big ? 1 : 0]);
  send(c, { t: 'joined', you: c.id, name: room.name, max: room.max, R: room.R,
            host: room.host === c.id, priv: room.pass ? 1 : 0, food: food });
  room.sendMeta();
}

function leaveRoom(c){
  const room = c.room;
  if(!room) return;
  if(c.snake) room.kill(c.snake, null, true);
  room.clients.delete(c.id);
  c.room = null; c.snake = null;
  if(room.clients.size === 0){
    room.destroy();
  } else {
    if(room.host === c.id) room.host = room.clients.keys().next().value;
    room.sendMeta();
  }
}

function roomList(){
  const a = [];
  for(const r of rooms.values()){
    a.push({ id: r.id, name: r.name, n: r.clients.size, max: r.max, priv: r.pass ? 1 : 0 });
  }
  return a;
}

/* ---------------- mensagens dos jogadores ---------------- */
function handle(c, m){
  switch(m.t){
    case 'list':
      send(c, { t: 'rooms', rooms: roomList() });
      break;

    case 'create': {
      if(c.room) return;
      if(rooms.size >= MAX_ROOMS) return sendErr(c, 'SERVIDOR CHEIO');
      const name = cleanName(m.name, 12) || ('SALA ' + nextRoomId);
      const priv = !!m.priv;
      const pass = priv ? cleanPass(m.pass) : '';
      if(priv && !pass) return sendErr(c, 'DEFINA UMA SENHA');
      const room = new Room(name, pass);
      rooms.set(room.id, room);
      joinRoom(c, room, cleanName(m.nick, 10) || 'JOGADOR');
      break;
    }

    case 'join': {
      if(c.room) return;
      const room = rooms.get(String(m.id));
      if(!room) return sendErr(c, 'SALA NAO EXISTE');
      if(room.clients.size >= room.max) return sendErr(c, 'SALA CHEIA');
      if(room.pass && room.pass !== cleanPass(m.pass)) return sendErr(c, 'SENHA ERRADA');
      joinRoom(c, room, cleanName(m.nick, 10) || 'JOGADOR');
      break;
    }

    case 'in':
      if(c.snake && typeof m.a === 'number' && isFinite(m.a)){
        c.snake.targetAngle = m.a;
        c.snake.wantBoost = !!m.b;
      }
      break;

    case 'respawn':
      if(c.room && !c.snake){
        let mass = START_MASS;
        const nowT = Date.now();
        // morte inválida cancelada pela guardiã do cliente: volta com o tamanho que tinha (1x a cada 30 s)
        if(m.keep && c.lastMass > START_MASS && nowT - (c.lastDeathT || 0) < 5000 && nowT - (c.lastRestoreT || 0) > 30000){
          mass = Math.min(c.lastMass, 3000);
          c.lastRestoreT = nowT;
        }
        c.room.spawn(c, mass);
        send(c, { t: 'respawned' });
      }
      break;

    case 'leave':
      leaveRoom(c);
      break;
  }
}

/* ---------------- servidor HTTP + WebSocket ---------------- */
const server = http.createServer(function(req, res){
  res.writeHead(200, { 'Content-Type': 'text/plain; charset=utf-8', 'Access-Control-Allow-Origin': '*' });
  let players = 0;
  for(const r of rooms.values()) players += r.clients.size;
  res.end('SNAKE.IO server ok | salas: ' + rooms.size + ' | jogadores: ' + players +
          ' | tick medio: ' + (tickCount ? (tickMsSum / tickCount).toFixed(2) : '0') + ' ms' +
          ' | guardiao: ' + GUARD_TOTAL.valid + ' mortes validas, ' + GUARD_TOTAL.blocked + ' bloqueadas');
});

const wss = new WebSocketServer({ server: server, maxPayload: 4096 });

wss.on('connection', function(ws, req){
  if(ALLOWED_ORIGIN && req.headers.origin !== ALLOWED_ORIGIN){
    ws.close(1008, 'origem nao permitida');
    return;
  }
  const c = { id: nextClientId++, ws: ws, nick: 'JOGADOR', room: null, snake: null, alive: true, cnt: 0, cntT: Date.now() };
  ws.__c = c;
  ws.on('pong', function(){ c.alive = true; });
  ws.on('message', function(data){
    const now = Date.now();
    if(now - c.cntT > 1000){ c.cntT = now; c.cnt = 0; }
    if(++c.cnt > 120){ ws.terminate(); return; }          // spam
    let m;
    try{ m = JSON.parse(String(data)); }catch(e){ return; }
    if(m && typeof m === 'object') handle(c, m);
  });
  ws.on('close', function(){ leaveRoom(c); });
  ws.on('error', function(){});
  send(c, { t: 'hello' });
});

// lista de salas para quem está no lobby
setInterval(function(){
  const msg = JSON.stringify({ t: 'rooms', rooms: roomList() });
  wss.clients.forEach(function(ws){
    if(ws.__c && !ws.__c.room && ws.readyState === 1){ try{ ws.send(msg); }catch(e){} }
  });
}, 2000);

// derruba conexões mortas
setInterval(function(){
  wss.clients.forEach(function(ws){
    if(ws.__c && !ws.__c.alive){ ws.terminate(); return; }
    if(ws.__c) ws.__c.alive = false;
    try{ ws.ping(); }catch(e){}
  });
}, 20000);

server.listen(PORT, function(){
  console.log('SNAKE.IO server rodando na porta ' + PORT);
});
