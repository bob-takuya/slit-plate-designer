// ============================================================
// Slit Plate Designer v3 — 正しい幾何学
//
// 根本的な設計変更:
//
//   [問題の核心]
//   球面上のプレート（法線=球の外法線）で直交するペアは
//   球の中心から90度離れた位置にあり、距離=R√2。
//   R=200mm, size=100mmでは物理的に交差不可能。
//
//   [正しい構造]
//   プレートは球を「横断」する（法線は球面の法線ではなく「スライス方向」）
//   - 法線N方向にdステップでスライス
//   - 各スライスの中心位置: N×t（tは[-maxT, maxT]）
//   - 接合条件: |t_A| ≤ size/2 AND |t_B| ≤ size/2
//   → この条件を守ることで全プレートが接合可能
//
//   拘束1: 干渉なし（OBB SAT 15軸）
//   拘束2: 全プレートが単一連結ネットワーク
//   目標:  密度（カバレッジ）を最大化
// ============================================================

const LOG = (msg) => {
  const el = document.getElementById('log');
  if (!el) return;
  el.textContent += msg + '\n';
  el.scrollTop = el.scrollHeight;
};
const STAT = (id, val) => { const el = document.getElementById(id); if (el) el.textContent = val; };
const V3 = THREE.Vector3;
const EPS = 1e-7;

// ============================================================
// 数学ヘルパー
// ============================================================
function v3dot(a, b)  { return a.x*b.x + a.y*b.y + a.z*b.z; }
function v3cross(a,b) { return new V3(a.y*b.z-a.z*b.y, a.z*b.x-a.x*b.z, a.x*b.y-a.y*b.x); }
function v3norm(v)    { const l=Math.sqrt(v3dot(v,v)); return l<EPS ? new V3(0,0,1) : new V3(v.x/l,v.y/l,v.z/l); }
function v3scale(v,s) { return new V3(v.x*s, v.y*s, v.z*s); }
function v3add(a,b)   { return new V3(a.x+b.x, a.y+b.y, a.z+b.z); }
function v3sub(a,b)   { return new V3(a.x-b.x, a.y-b.y, a.z-b.z); }

// 2D 線分間の最小距離
function seg2dMinDist(a0, a1, b0, b1) {
  function ptSeg(pu, pv, s0, s1) {
    const dx=s1.u-s0.u, dy=s1.v-s0.v, l2=dx*dx+dy*dy;
    if (l2<EPS) return Math.hypot(pu-s0.u, pv-s0.v);
    const t=Math.max(0,Math.min(1,((pu-s0.u)*dx+(pv-s0.v)*dy)/l2));
    return Math.hypot(pu-(s0.u+t*dx), pv-(s0.v+t*dy));
  }
  // 交差チェック
  function cross2d(ax,ay,bx,by){ return ax*by-ay*bx; }
  const dax=a1.u-a0.u, day=a1.v-a0.v;
  const dbx=b1.u-b0.u, dby=b1.v-b0.v;
  const dx=b0.u-a0.u, dy=b0.v-a0.v;
  const den=cross2d(dax,day,dbx,dby);
  if (Math.abs(den)>EPS) {
    const t=cross2d(dx,dy,dbx,dby)/den;
    const s=cross2d(dx,dy,dax,day)/den;
    if (t>=-EPS&&t<=1+EPS&&s>=-EPS&&s<=1+EPS) return 0;
  }
  return Math.min(ptSeg(a0.u,a0.v,b0,b1), ptSeg(a1.u,a1.v,b0,b1),
                  ptSeg(b0.u,b0.v,a0,a1), ptSeg(b1.u,b1.v,a0,a1));
}

// ============================================================
// OBB-OBB 干渉判定（SAT 15軸）
// ============================================================
function obbIntersect(cA, axA, hA, cB, axB, hB) {
  const D = v3sub(cB, cA);
  const axes = [...axA, ...axB];
  for (const a of axA) for (const b of axB) {
    const c = v3cross(a, b);
    if (v3dot(c,c) > EPS) axes.push(v3norm(c));
  }
  for (const ax of axes) {
    const len2 = v3dot(ax,ax);
    if (len2 < EPS) continue;
    const n = len2 > 1+EPS ? v3norm(ax) : ax;
    let rA=0, rB=0;
    for (let i=0;i<3;i++) rA += hA[i]*Math.abs(v3dot(axA[i],n));
    for (let i=0;i<3;i++) rB += hB[i]*Math.abs(v3dot(axB[i],n));
    if (Math.abs(v3dot(D,n)) > rA+rB+EPS) return false;
  }
  return true;
}

// ============================================================
// Plate クラス
// ============================================================
class Plate {
  constructor(id, center, normal, size, thick) {
    this.id = id;
    this.center = center.clone();
    this.normal = v3norm(normal);
    this.size = size;
    this.thick = thick;
    this.slits = [];
    this.neighbors = [];
    this.groupId = 0;
    this._buildFrame();
  }

  _buildFrame() {
    const ref = Math.abs(this.normal.y) < 0.9 ? new V3(0,1,0) : new V3(1,0,0);
    this.u = v3norm(v3cross(this.normal, ref));
    this.v = v3norm(v3cross(this.normal, this.u));
  }

  localToWorld(pu, pv) {
    return v3add(v3add(v3scale(this.u, pu), v3scale(this.v, pv)), this.center);
  }

  worldToLocal(pt) {
    const d = v3sub(pt, this.center);
    return { u: v3dot(d, this.u), v: v3dot(d, this.v) };
  }

  inBounds(pu, pv, margin=0) {
    const h = this.size/2 - margin;
    return Math.abs(pu) <= h && Math.abs(pv) <= h;
  }

  corners() {
    const h = this.size/2;
    return [[-h,-h],[h,-h],[h,h],[-h,h]].map(([u,v]) => this.localToWorld(u,v));
  }

  obbParams() {
    return {
      c: this.center,
      ax: [this.u, this.v, this.normal],
      h:  [this.size/2, this.size/2, this.thick/2]
    };
  }

  intersects(other) {
    const a = this.obbParams(), b = other.obbParams();
    return obbIntersect(a.c, a.ax, a.h, b.c, b.ax, b.h);
  }
}

// ============================================================
// スリット幾何計算
// ============================================================
function computeSlits(pA, pB, tol) {
  // 2平面の交差線
  const lineDir = v3norm(v3cross(pA.normal, pB.normal));
  if (v3dot(lineDir, lineDir) < 0.01) return null;

  const dA = v3dot(pA.normal, pA.center);
  const dB = v3dot(pB.normal, pB.center);
  const n12 = v3dot(pA.normal, pB.normal);
  const det = 1 - n12*n12;
  if (Math.abs(det) < EPS) return null;
  const c1=(dA-n12*dB)/det, c2=(dB-n12*dA)/det;
  const linePoint = v3add(v3scale(pA.normal,c1), v3scale(pB.normal,c2));

  const tA = projectOnLine(pA, linePoint, lineDir);
  const tB = projectOnLine(pB, linePoint, lineDir);
  if (!tA || !tB) return null;

  const tMin = Math.max(tA[0], tB[0]);
  const tMax = Math.min(tA[1], tB[1]);
  if (tMax - tMin < Math.max(pA.thick, pB.thick) * 2.5) return null;

  const sA = buildSlit(pA, pB, linePoint, lineDir, tMin, tMax, tol);
  const sB = buildSlit(pB, pA, linePoint, lineDir, tMin, tMax, tol);
  if (!sA || !sB) return null;
  return { slitA: sA, slitB: sB };
}

function projectOnLine(plate, linePoint, lineDir) {
  const ts = plate.corners().map(c => v3dot(v3sub(c, linePoint), lineDir));
  const lo = Math.min(...ts), hi = Math.max(...ts);
  const mid = v3add(linePoint, v3scale(lineDir, (lo+hi)*0.5));
  const loc = plate.worldToLocal(mid);
  if (!plate.inBounds(loc.u, loc.v, plate.size*0.02)) return null;
  return [lo, hi];
}

function buildSlit(host, inserted, linePoint, lineDir, tMin, tMax, tol) {
  const h = host.size/2;
  const le = host.worldToLocal(v3add(linePoint, v3scale(lineDir, tMin)));
  const lx = host.worldToLocal(v3add(linePoint, v3scale(lineDir, tMax)));
  const cl = p => ({ u:Math.max(-h,Math.min(h,p.u)), v:Math.max(-h,Math.min(h,p.v)) });
  const ce=cl(le), cx=cl(lx);
  const du=cx.u-ce.u, dv=cx.v-ce.v;
  const w = inserted.thick*tol;
  if (Math.sqrt(du*du+dv*dv) < w*2.5) return null;

  const dte = h - Math.max(Math.abs(ce.u), Math.abs(ce.v));
  const dtx = h - Math.max(Math.abs(cx.u), Math.abs(cx.v));
  let entry, exit;
  if (dte <= dtx) { entry = snapEdge(ce, cx, h); exit = cx; }
  else            { entry = snapEdge(cx, ce, h); exit = ce; }

  if (!host.inBounds(exit.u, exit.v, w*0.5)) return null;

  return { host, inserted, entry, exit, width: w };
}

function snapEdge(pt, other, h) {
  const du=other.u-pt.u, dv=other.v-pt.v;
  const len=Math.sqrt(du*du+dv*dv);
  if (len<EPS) return {u:Math.sign(pt.u||1)*h, v:pt.v};
  let t=Infinity;
  const tryT=(tv)=>{ if(tv>EPS) t=Math.min(t,tv); };
  if(Math.abs(du)>EPS){ tryT((h-pt.u)/du); tryT((-h-pt.u)/du); }
  if(Math.abs(dv)>EPS){ tryT((h-pt.v)/dv); tryT((-h-pt.v)/dv); }
  if(!isFinite(t)) return pt;
  return {u:pt.u+du*t, v:pt.v+dv*t};
}

function slitsOverlap(s1, s2) {
  const clearance = (s1.width + s2.width)*0.5;
  return seg2dMinDist(s1.entry, s1.exit, s2.entry, s2.exit) < clearance;
}

// ============================================================
// 直交フレーム群（5フレーム×3軸=15方向）
// 各フレーム内の3軸は互いに直交 → 同フレーム内の異なる軸のプレートは接合可能
// ============================================================
function getFrames() {
  const r = Math.SQRT1_2;
  return [
    // フレーム0: 標準 XYZ
    [new V3(1,0,0), new V3(0,1,0), new V3(0,0,1)],
    // フレーム1: Y軸周り 45°
    [new V3(r,0,r), new V3(0,1,0), new V3(-r,0,r)],
    // フレーム2: Z軸周り 45°
    [new V3(r,r,0), new V3(-r,r,0), new V3(0,0,1)],
    // フレーム3: X軸周り 45°
    [new V3(1,0,0), new V3(0,r,r), new V3(0,-r,r)],
    // フレーム4: 全軸 45° (体対角線)
    [new V3(r,0,r), new V3(-r,0,r), new V3(0,1,0)],  // フレーム1と同様だが順序違い
  ];
}

// ============================================================
// プレート生成（球横断スライス方式）
//
// 接合可能条件（導出済み）:
//   法線N_A方向の中心位置t_Aと
//   法線N_B方向の中心位置t_B（N_A⊥N_B）が
//   同時に |t_A| ≤ size/2 かつ |t_B| ≤ size/2 を満たす場合のみ接合可能
//
// → スライス位置を |t| ≤ size/2 の範囲に制限する
// ============================================================
function generatePlates(radius, size, thick, spacing) {
  const frames = getFrames();
  const maxT = size * 0.5; // 接合可能な最大オフセット
  const plates = [];
  let id = 0;

  frames.forEach((axes, fi) => {
    axes.forEach((normal, ai) => {
      const gid = fi * 3 + ai;
      // |t| ≤ maxT の範囲でスライス（接合可能性保証）
      for (let t = 0; t <= maxT; t += spacing) {
        const ts = t === 0 ? [0] : [t, -t]; // 対称に配置
        for (const tv of ts) {
          if (Math.abs(tv) >= radius) continue; // 球の外
          const r2 = radius*radius - tv*tv;
          if (r2 < (size*0.1)*(size*0.1)) continue; // 断面が小さすぎ
          const p = new Plate(id++, v3scale(normal, tv), v3norm(normal), size, thick);
          p.groupId = gid;
          plates.push(p);
        }
      }
    });
  });
  return plates;
}

// ============================================================
// 1スペーシングでのレイアウト評価
// ============================================================
function evaluateSpacing(radius, size, thick, spacing, slitTol) {
  const all = generatePlates(radius, size, thick, spacing);

  // 干渉チェック（OBB SAT厳密判定）
  // 直交ペア（後にスリット接合）は干渉OKとみなす
  const rejected = new Set();
  for (let i = 0; i < all.length; i++) {
    if (rejected.has(i)) continue;
    for (let j = i+1; j < all.length; j++) {
      if (rejected.has(j)) continue;
      if (!all[i].intersects(all[j])) continue; // 干渉なし
      // 干渉あり → 直交ならスリット接合で解決できるか確認
      const dot = Math.abs(v3dot(all[i].normal, all[j].normal));
      if (dot < 0.1) continue; // 直交 → スリット接合で解決（後で計算）
      // 非直交で干渉 → jを除外
      rejected.add(j);
    }
  }
  const plates = all.filter((_,i) => !rejected.has(i));

  // スリット計算
  for (let i = 0; i < plates.length; i++) {
    for (let j = i+1; j < plates.length; j++) {
      const pA = plates[i], pB = plates[j];
      if (Math.abs(v3dot(pA.normal, pB.normal)) > 0.1) continue; // 非直交スキップ
      const dist = pA.center.distanceTo(pB.center);
      if (dist > size * Math.SQRT2 * 1.2) continue; // 距離カリング
      const res = computeSlits(pA, pB, slitTol);
      if (!res) continue;
      // 既存スリットとの重複チェック
      let ok = true;
      for (const s of pA.slits) if (slitsOverlap(s, res.slitA)) { ok=false; break; }
      if (ok) for (const s of pB.slits) if (slitsOverlap(s, res.slitB)) { ok=false; break; }
      if (!ok) continue;
      pA.slits.push(res.slitA); pB.slits.push(res.slitB);
      pA.neighbors.push(pB.id); pB.neighbors.push(pA.id);
    }
  }

  // 最大連結成分
  const idMap = new Map(plates.map(p => [p.id, p]));
  const visited = new Set();
  let bestComp = [];
  plates.forEach(p => {
    if (visited.has(p.id)) return;
    const comp = [], q = [p.id];
    while (q.length) {
      const id = q.shift();
      if (visited.has(id)) continue;
      visited.add(id); comp.push(id);
      (idMap.get(id)?.neighbors || []).forEach(n => { if (!visited.has(n)) q.push(n); });
    }
    if (comp.length > bestComp.length) bestComp = comp;
  });

  const bestSet = new Set(bestComp);
  const final = plates.filter(p => bestSet.has(p.id));
  final.forEach(p => {
    p.slits     = p.slits.filter(s => bestSet.has(s.inserted.id));
    p.neighbors = p.neighbors.filter(id => bestSet.has(id));
  });

  return {
    plates: final,
    totalCandidates: all.length,
    validBeforeConnect: plates.length,
    connected: bestComp.length === plates.length && plates.length > 0,
    connectRatio: plates.length > 0 ? bestComp.length / plates.length : 0,
    slitCount: final.reduce((s,p)=>s+p.slits.length,0)/2,
    spacing
  };
}

// ============================================================
// 最適スペーシング探索
// 拘束: 干渉ゼロ + 全連結
// 目標: プレート数（密度）最大化
// ============================================================
async function findOptimal(radius, size, thick, slitTol, maxPlates) {
  LOG('▶ 探索開始');
  LOG(`接合可能範囲: |t| ≤ ${(size*0.5).toFixed(0)}mm`);

  let bestResult = null, bestCount = 0;

  // 粗いグリッドサーチ（広→密）
  const spacings = [];
  for (let s = size * 0.9; s >= thick * 2.2; s *= 0.82) spacings.push(s);
  LOG(`探索点数: ${spacings.length} (${spacings[0].toFixed(1)}mm → ${spacings[spacings.length-1].toFixed(1)}mm)`);

  for (const sp of spacings) {
    const res = evaluateSpacing(radius, size, thick, sp, slitTol);
    const mark = res.connected ? '✓' : '—';
    LOG(`  間隔${sp.toFixed(1).padStart(6)}: ${String(res.plates.length).padStart(3)}枚 `+
        `スリット${Math.round(res.slitCount)}対 `+
        `連結${(res.connectRatio*100).toFixed(0)}% ${mark}`);

    if (res.connected && res.plates.length > bestCount) {
      bestCount = res.plates.length;
      bestResult = res;
    }
    if (res.plates.length >= maxPlates && res.connected) break;
    await new Promise(r => setTimeout(r, 1));
  }

  if (!bestResult) {
    // 全連結が取れない場合、最大連結比を持つ結果を返す
    LOG('⚠ 全連結解なし。最大連結成分で近似します。');
    let bestRatio = 0;
    for (const sp of spacings) {
      const res = evaluateSpacing(radius, size, thick, sp, slitTol);
      if (res.connectRatio > bestRatio) { bestRatio = res.connectRatio; bestResult = res; }
      await new Promise(r => setTimeout(r, 1));
    }
    return bestResult;
  }

  // 精密化（最良点周辺で二分探索）
  LOG(`精密化: 最良間隔 ${bestResult.spacing.toFixed(1)}mm 周辺`);
  let lo = bestResult.spacing * 0.88, hi = bestResult.spacing * 1.12;
  for (let iter = 0; iter < 10; iter++) {
    const mid = (lo + hi) * 0.5;
    const res = evaluateSpacing(radius, size, thick, mid, slitTol);
    if (res.connected && res.plates.length >= bestResult.plates.length) {
      bestResult = res; hi = mid;
    } else {
      lo = mid;
    }
    await new Promise(r => setTimeout(r, 1));
  }

  LOG(`✓ 最適間隔: ${bestResult.spacing.toFixed(2)}mm → ${bestResult.plates.length}枚`);
  return bestResult;
}

// ============================================================
// メイン
// ============================================================
let PLATES = [];

async function runOptimize() {
  const size      = +document.getElementById('plateSize').value;
  const thick     = +document.getElementById('plateThick').value;
  const radius    = +document.getElementById('targetRadius').value;
  const maxPlates = +document.getElementById('density').value;
  const slitTol   = +document.getElementById('slitTol').value;

  document.getElementById('log').textContent = '';
  LOG(`設定: R=${radius}mm, size=${size}mm, thick=${thick}mm`);

  const result = await findOptimal(radius, size, thick, slitTol, maxPlates);

  if (!result || !result.plates.length) {
    LOG('❌ 解が見つかりません。size を radius の 50〜100% 程度に設定してください。');
    return;
  }

  PLATES = result.plates;
  const sphereArea = 4 * Math.PI * radius * radius;
  STAT('st-plates',    PLATES.length);
  STAT('st-slits',     Math.round(result.slitCount));
  STAT('st-connected', result.connected ? `✓ ${PLATES.length}枚` : `${PLATES.length}枚 (部分連結)`);
  STAT('st-coverage',  (PLATES.length * size * size / sphereArea * 100).toFixed(1) + '%');

  renderScene(PLATES, radius);
  LOG('✓ 完了');
}

// ============================================================
// Three.js レンダリング
// ============================================================
let scene, camera, renderer;

function initRenderer() {
  const canvas = document.getElementById('canvas3d');
  renderer = new THREE.WebGLRenderer({ canvas, antialias: true });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
  renderer.setClearColor(0x1a1a2e);
  window.renderer = renderer;

  scene = new THREE.Scene();
  camera = new THREE.PerspectiveCamera(60, canvas.clientWidth/canvas.clientHeight, 1, 10000);
  camera.position.set(0, 200, 700);
  window.camera = camera;

  scene.add(new THREE.AmbientLight(0xffffff, 0.45));
  const dir = new THREE.DirectionalLight(0xffffff, 0.8);
  dir.position.set(1,2,1.5); scene.add(dir);

  // マウス操作
  let drag=false, rDrag=false, lx=0, ly=0;
  const sph={theta:0.3,phi:1.0,r:700};
  const tgt=new THREE.Vector3();
  function uc() {
    camera.position.set(
      tgt.x+sph.r*Math.sin(sph.phi)*Math.sin(sph.theta),
      tgt.y+sph.r*Math.cos(sph.phi),
      tgt.z+sph.r*Math.sin(sph.phi)*Math.cos(sph.theta)
    );
    camera.lookAt(tgt);
  }
  uc();
  canvas.addEventListener('mousedown', e=>{drag=true;rDrag=e.button===2;lx=e.clientX;ly=e.clientY;e.preventDefault();});
  canvas.addEventListener('contextmenu', e=>e.preventDefault());
  window.addEventListener('mouseup', ()=>drag=false);
  window.addEventListener('mousemove', e=>{
    if(!drag)return;
    const dx=e.clientX-lx, dy=e.clientY-ly; lx=e.clientX; ly=e.clientY;
    if(rDrag){ const r=new THREE.Vector3().crossVectors(camera.getWorldDirection(new THREE.Vector3()),camera.up).normalize(); tgt.addScaledVector(r,-dx*0.5).addScaledVector(camera.up,dy*0.5); }
    else{ sph.theta-=dx*0.005; sph.phi=Math.max(0.1,Math.min(Math.PI-0.1,sph.phi+dy*0.005)); }
    uc();
  });
  canvas.addEventListener('wheel', e=>{sph.r=Math.max(80,sph.r+e.deltaY*0.5);uc();});
  // タッチ
  let lT=[];
  canvas.addEventListener('touchstart',e=>{lT=[...e.touches];e.preventDefault();},{passive:false});
  canvas.addEventListener('touchmove',e=>{
    e.preventDefault();
    if(e.touches.length===1&&lT.length>=1){ sph.theta-=(e.touches[0].clientX-lT[0].clientX)*0.005; sph.phi=Math.max(0.1,Math.min(Math.PI-0.1,sph.phi+(e.touches[0].clientY-lT[0].clientY)*0.005)); uc(); }
    else if(e.touches.length===2&&lT.length===2){ const d0=Math.hypot(lT[0].clientX-lT[1].clientX,lT[0].clientY-lT[1].clientY); const d1=Math.hypot(e.touches[0].clientX-e.touches[1].clientX,e.touches[0].clientY-e.touches[1].clientY); if(d0>1){sph.r=Math.max(80,sph.r*d0/d1);uc();} }
    lT=[...e.touches];
  },{passive:false});
  canvas.addEventListener('touchend',e=>{lT=[...e.touches];});
  window.addEventListener('resize', ()=>{ camera.aspect=canvas.clientWidth/canvas.clientHeight; camera.updateProjectionMatrix(); renderer.setSize(canvas.clientWidth,canvas.clientHeight,false); });
  renderer.setSize(canvas.clientWidth,canvas.clientHeight,false);
  animate();
}

function animate(){ requestAnimationFrame(animate); renderer.render(scene,camera); }

// groupId で色分け（5フレーム×3軸）
const GCOLS = [
  0x4fc3f7,0xf48fb1,0xa5d6a7,  // フレーム0 XYZ
  0x80deea,0xf8bbd0,0xc8e6c9,  // フレーム1
  0x00bcd4,0xe91e63,0x66bb6a,  // フレーム2
  0x0097a7,0xad1457,0x388e3c,  // フレーム3
  0xffe082,0xffab40,0xd7ccc8,  // フレーム4
];

function renderScene(plates, radius) {
  for(let i=scene.children.length-1;i>=0;i--){ if(!scene.children[i].isLight) scene.remove(scene.children[i]); }
  scene.add(new THREE.Mesh(new THREE.SphereGeometry(radius,36,18), new THREE.MeshBasicMaterial({color:0x2a3a4a,wireframe:true,transparent:true,opacity:0.10})));
  scene.add(new THREE.AxesHelper(80));

  const mats = GCOLS.map(c => new THREE.MeshLambertMaterial({color:c,transparent:true,opacity:0.75,side:THREE.DoubleSide}));
  const slitMat = new THREE.MeshBasicMaterial({color:0xffff00,side:THREE.DoubleSide});

  plates.forEach(p => {
    const m = new THREE.Mesh(new THREE.PlaneGeometry(p.size,p.size), mats[p.groupId%mats.length]);
    m.position.copy(p.center);
    m.quaternion.setFromUnitVectors(new THREE.Vector3(0,0,1), p.normal);
    scene.add(m);
    p.slits.forEach(s=>{
      const e=s.entry,x=s.exit,du=x.u-e.u,dv=x.v-e.v,len=Math.sqrt(du*du+dv*dv);
      if(len<EPS)return;
      const sm=new THREE.Mesh(new THREE.PlaneGeometry(s.width,len),slitMat);
      sm.position.copy(p.localToWorld((e.u+x.u)*.5,(e.v+x.v)*.5));
      sm.quaternion.setFromUnitVectors(new THREE.Vector3(0,0,1),p.normal);
      sm.rotateZ(Math.atan2(du,dv));
      scene.add(sm);
    });
  });
}

// ============================================================
// Export
// ============================================================
function exportCSV() {
  if (!PLATES.length) { alert('先に最適化を実行してください'); return; }
  const rows=['id,cx,cy,cz,nx,ny,nz,group_id,num_slits'];
  PLATES.forEach((p,i)=>rows.push([i,p.center.x.toFixed(2),p.center.y.toFixed(2),p.center.z.toFixed(2),p.normal.x.toFixed(4),p.normal.y.toFixed(4),p.normal.z.toFixed(4),p.groupId,p.slits.length].join(',')));
  rows.push('','plate_id,slit_idx,other_plate_id,entry_u,entry_v,exit_u,exit_v,width_mm');
  PLATES.forEach((p,i)=>p.slits.forEach((s,si)=>rows.push([i,si,s.inserted.id,s.entry.u.toFixed(2),s.entry.v.toFixed(2),s.exit.u.toFixed(2),s.exit.v.toFixed(2),s.width.toFixed(3)].join(','))));
  download('slit_plates.csv',rows.join('\n'),'text/csv');
}

function exportDXF() {
  if (!PLATES.length) { alert('先に最適化を実行してください'); return; }
  const cols=+document.getElementById('dxfCols').value;
  const sp=+document.getElementById('dxfSpacing').value;
  const size=PLATES[0].size;
  let dxf='';
  [...PLATES].sort((a,b)=>a.groupId-b.groupId).forEach((p,idx)=>{
    const col=idx%cols,row=Math.floor(idx/cols),ox=col*(size+sp),oy=-row*(size+sp),h=size/2;
    dxf+=dxfRect(ox-h,oy-h,ox+h,oy+h,`G${p.groupId}`);
    p.slits.forEach(s=>{
      const eu=s.entry.u+ox,ev=s.entry.v+oy,xu=s.exit.u+ox,xv=s.exit.v+oy,hw=s.width/2;
      const du=xu-eu,dv=xv-ev,len=Math.sqrt(du*du+dv*dv);
      if(len<EPS)return;
      const nx=-dv/len*hw,ny=du/len*hw;
      dxf+=dxfLine(eu+nx,ev+ny,xu+nx,xv+ny,'SLITS')+dxfLine(xu+nx,xv+ny,xu-nx,xv-ny,'SLITS')+dxfLine(xu-nx,xv-ny,eu-nx,ev-ny,'SLITS')+dxfLine(eu-nx,ev-ny,eu+nx,ev+ny,'SLITS');
    });
    dxf+=dxfText(ox-h+2,oy-h+2,String(idx+1),`G${p.groupId}`,size*0.08);
  });
  dxf+='ENDSEC\n0\nEOF\n';
  download('slit_plates.dxf',dxfHeader()+dxf,'application/dxf');
}

function dxfHeader(){return`0\nSECTION\n2\nHEADER\n9\n$INSUNITS\n70\n4\n0\nENDSEC\n0\nSECTION\n2\nENTITIES\n`;}
function dxfRect(x1,y1,x2,y2,l){return dxfLine(x1,y1,x2,y1,l)+dxfLine(x2,y1,x2,y2,l)+dxfLine(x2,y2,x1,y2,l)+dxfLine(x1,y2,x1,y1,l);}
function dxfLine(x1,y1,x2,y2,l){return`0\nLINE\n8\n${l}\n10\n${x1.toFixed(4)}\n20\n${y1.toFixed(4)}\n30\n0.0\n11\n${x2.toFixed(4)}\n21\n${y2.toFixed(4)}\n31\n0.0\n`;}
function dxfText(x,y,t,l,h){return`0\nTEXT\n8\n${l}\n10\n${x.toFixed(4)}\n20\n${y.toFixed(4)}\n30\n0.0\n40\n${h.toFixed(4)}\n1\n${t}\n`;}

function exportTopView() {
  if (!PLATES.length) { alert('先に最適化を実行してください'); return; }
  const scale=+document.getElementById('topScale').value, size=PLATES[0].size;
  const r=+document.getElementById('targetRadius').value;
  const dim=Math.ceil((r*2+size)*scale*1.1);
  const canvas=document.getElementById('topview-canvas');
  canvas.width=dim; canvas.height=dim;
  const ctx=canvas.getContext('2d');
  ctx.fillStyle='#1a1a2e'; ctx.fillRect(0,0,dim,dim);
  const cx=dim/2,cy=dim/2;
  PLATES.forEach((p,i)=>{
    const x=cx+p.center.x*scale,y=cy-p.center.z*scale,half=size*scale/2;
    const col='#'+GCOLS[p.groupId%GCOLS.length].toString(16).padStart(6,'0');
    ctx.fillStyle=col+'aa'; ctx.strokeStyle=col; ctx.lineWidth=1;
    ctx.fillRect(x-half,y-half,half*2,half*2); ctx.strokeRect(x-half,y-half,half*2,half*2);
    ctx.fillStyle='#fff'; ctx.font=`${Math.max(8,size*scale*0.2)}px monospace`; ctx.textAlign='center';
    ctx.fillText(String(i+1),x,y+4);
  });
  canvas.toBlob(blob=>{const url=URL.createObjectURL(blob),a=document.createElement('a');a.href=url;a.download='slit_plates_topview.png';a.click();URL.revokeObjectURL(url);});
}

function download(filename,content,mime){const blob=new Blob([content],{type:mime}),url=URL.createObjectURL(blob),a=document.createElement('a');a.href=url;a.download=filename;a.click();URL.revokeObjectURL(url);}

initRenderer();
