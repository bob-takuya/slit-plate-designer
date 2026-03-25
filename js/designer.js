// ============================================================
// Slit Plate Designer v8
//
// Algorithm:
//  1. Seed plate: random position on sphere, random tangential normal
//  2. Greedy growth with random sampling + line-search optimization:
//     - Each step: N_RANDOM trials of (pA=random, θ=random)
//     - For each trial: line-search on step distance → best sphere coverage
//     - Constraints checked strictly: slit valid + no interference
//     - Best candidate (max min-distance to existing = PDS criterion) is added
//  3. Repeat until no valid candidate found
//
// Key fix over v1-v7: clipLineToPlate uses parametric slab clipping
// (replaces broken OBB-corner projection).
// ============================================================

const LOG = (msg) => {
  const el = document.getElementById('log');
  if (!el) return;
  el.textContent += msg + '\n';
  el.scrollTop = el.scrollHeight;
};
const STAT = (id, val) => { const el = document.getElementById(id); if (el) el.textContent = val; };

// ============================================================
// Math Helpers
// ============================================================
const V3 = THREE.Vector3;

function dot(a, b) { return a.x*b.x + a.y*b.y + a.z*b.z; }
function cross(a, b) { return new V3(a.y*b.z-a.z*b.y, a.z*b.x-a.x*b.z, a.x*b.y-a.y*b.x); }
function sub(a, b)   { return new V3(a.x-b.x, a.y-b.y, a.z-b.z); }
function add(a, b)   { return new V3(a.x+b.x, a.y+b.y, a.z+b.z); }
function scale(v, s) { return new V3(v.x*s, v.y*s, v.z*s); }
function normalize(v) { const l=Math.sqrt(dot(v,v)); return l<1e-12?new V3(0,0,1):scale(v,1/l); }
function vlen(v) { return Math.sqrt(dot(v,v)); }
function vdist(a, b) { return vlen(sub(a,b)); }

// Seeded LCG random number generator
function makeRng(seed) {
  let s = ((seed|0) >>> 0) + 1;
  return () => { s = Math.imul(1664525, s) + 1013904223 | 0; return (s >>> 0) / 4294967296; };
}

// ============================================================
// Plate class
// ============================================================
class Plate {
  constructor(id, center, normal, size, thickness) {
    this.id = id;
    this.center = center.clone();
    this.normal = normalize(normal);
    this.size = size;
    this.thick = thickness;
    this.slits = [];
    this.neighbors = [];
    this._buildFrame();
  }
  _buildFrame() {
    const n = this.normal;
    const helper = Math.abs(n.y) < 0.9 ? new V3(0,1,0) : new V3(1,0,0);
    this.u = normalize(cross(n, helper));
    this.v = normalize(cross(n, this.u));
  }
  localToWorld(pu, pv, pn=0) {
    return add(add(add(scale(this.u,pu), scale(this.v,pv)), scale(this.normal,pn)), this.center);
  }
  worldToLocal(pt) {
    const d = sub(pt, this.center);
    return { u: dot(d,this.u), v: dot(d,this.v), n: dot(d,this.normal) };
  }
  inBounds(pu, pv, margin=0) { const h=this.size/2-margin; return Math.abs(pu)<=h && Math.abs(pv)<=h; }
  obb() { return { center: this.center, axes: [this.u, this.v, this.normal], halfExtents: [this.size/2, this.size/2, this.thick/2] }; }
  obbCorners() {
    const corners=[], h=this.size/2, ht=this.thick/2;
    for(const su of[-1,1]) for(const sv of[-1,1]) for(const sn of[-1,1])
      corners.push(this.localToWorld(su*h, sv*h, sn*ht));
    return corners;
  }
}

// ============================================================
// OBB-OBB Intersection (SAT, 15 axes)
// ============================================================
function obbIntersect(A, B) {
  const D = sub(B.center, A.center);
  const axes = [...A.axes, ...B.axes];
  for(const a of A.axes) for(const b of B.axes) { const c=cross(a,b); if(dot(c,c)>1e-10) axes.push(normalize(c)); }
  for(const ax of axes) {
    let pA=0; for(let i=0;i<3;i++) pA += A.halfExtents[i]*Math.abs(dot(A.axes[i],ax));
    let pB=0; for(let i=0;i<3;i++) pB += B.halfExtents[i]*Math.abs(dot(B.axes[i],ax));
    if(Math.abs(dot(D,ax)) > pA+pB+1e-6) return false;
  }
  return true;
}

// ============================================================
// Plane-plane intersection line
// ============================================================
function planeIntersectionLine(pA, pB) {
  const lineDir = normalize(cross(pA.normal, pB.normal));
  if(dot(lineDir,lineDir) < 0.01) return null;
  const dA=dot(pA.normal,pA.center), dB=dot(pB.normal,pB.center);
  const n1n2=dot(pA.normal,pB.normal), det=1-n1n2*n1n2;
  if(Math.abs(det)<1e-8) return null;
  const c1=(dA-n1n2*dB)/det, c2=(dB-n1n2*dA)/det;
  return { linePoint: add(scale(pA.normal,c1), scale(pB.normal,c2)), lineDir };
}

// ============================================================
// KEY FIX: Parametric slab clipping (replaces broken OBB-corner projection)
// Finds [tMin, tMax] range where the line passes through the plate face.
// ============================================================
function clipLineToPlate(plate, linePoint, lineDir) {
  const lp  = sub(linePoint, plate.center);
  const pu0 = dot(lp, plate.u),  du = dot(lineDir, plate.u);
  const pv0 = dot(lp, plate.v),  dv = dot(lineDir, plate.v);
  const h   = plate.size / 2;
  let tMin=-1e9, tMax=1e9;

  if(Math.abs(du) < 1e-9) { if(Math.abs(pu0) > h+1e-4) return null; }
  else { const t1=(-h-pu0)/du, t2=(h-pu0)/du; tMin=Math.max(tMin,Math.min(t1,t2)); tMax=Math.min(tMax,Math.max(t1,t2)); }

  if(Math.abs(dv) < 1e-9) { if(Math.abs(pv0) > h+1e-4) return null; }
  else { const t1=(-h-pv0)/dv, t2=(h-pv0)/dv; tMin=Math.max(tMin,Math.min(t1,t2)); tMax=Math.min(tMax,Math.max(t1,t2)); }

  if(tMax-tMin < 1e-6) return null;
  return [tMin, tMax];
}

// ============================================================
// Slit geometry helpers
// ============================================================

// ptをcenterとは逆方向（外側）にスナップしてホストのエッジに当てる。
// entry点をMから外側に押し出す用途。
function snapAwayToEdge(pt, center, half) {
  const du = pt.u - center.u, dv = pt.v - center.v;
  const len = Math.sqrt(du * du + dv * dv);
  if (len < 1e-9) return { u: Math.sign(pt.u || 1) * half, v: pt.v };
  const clamp = t => Math.max(0, t);  // 負のtは無視（内側方向）
  let t = Infinity;
  if (Math.abs(du) > 1e-9) {
    const tA = (half  - pt.u) / du; if (tA >= -1e-6) t = Math.min(t, clamp(tA));
    const tB = (-half - pt.u) / du; if (tB >= -1e-6) t = Math.min(t, clamp(tB));
  }
  if (Math.abs(dv) > 1e-9) {
    const tA = (half  - pt.v) / dv; if (tA >= -1e-6) t = Math.min(t, clamp(tA));
    const tB = (-half - pt.v) / dv; if (tB >= -1e-6) t = Math.min(t, clamp(tB));
  }
  return isFinite(t) ? { u: pt.u + du * t, v: pt.v + dv * t } : pt;
}

// ユーザーの指摘通りの正しいスリットジオメトリ:
//   M   = オーバーラップ [tMin,tMax] の真の中点（2枚が交差する点）
//   exit = M（スリットの切断端点）
//   entry = Mから外側方向にプレートエッジまで延ばした点
//   → ペアのスリットは必ずM（同一の世界座標点）に向かい、等長になる
function buildSlitOnPlate(host, inserted, linePoint, lineDir, tMin, tMax, tol) {
  const half = host.size / 2;

  // M: オーバーラップ区間の真の中点（世界座標→ローカル座標）
  const tMid  = (tMin + tMax) / 2;
  const lMid  = host.worldToLocal(add(linePoint, scale(lineDir, tMid)));   // M in host frame
  const lNear = host.worldToLocal(add(linePoint, scale(lineDir, tMin)));   // tMin side
  const lFar  = host.worldToLocal(add(linePoint, scale(lineDir, tMax)));   // tMax side

  const distToEdge = p => half - Math.max(Math.abs(p.u), Math.abs(p.v));

  // エッジに近い方のオーバーラップ端点をエントリー側として選ぶ
  const lSide = distToEdge(lNear) <= distToEdge(lFar) ? lNear : lFar;

  // Mから外向き方向にスナップしてプレートの物理エッジへ
  const entry = snapAwayToEdge(lSide, lMid, half);
  // exit = M（切断端点）
  const exit  = { u: lMid.u, v: lMid.v };

  // 検証
  if (distToEdge(entry) > host.size * 0.03) return null;  // エッジ上でない
  if (!host.inBounds(exit.u, exit.v, host.thick * 0.5))  return null;  // Mが範囲内か
  const du = exit.u - entry.u, dv = exit.v - entry.v;
  if (Math.sqrt(du * du + dv * dv) < inserted.thick * 2)  return null;  // スリットが短すぎ

  return { host, inserted, entry, exit, width: inserted.thick * tol };
}

// スリット切断端点 = exit そのもの（= M）
// 以前は (entry+exit)/2 を使っていたが、exitをMに変えたのでそのまま返す
function slitCutExit(s) {
  return { u: s.exit.u, v: s.exit.v };
}

// ============================================================
// Compute slits between two plates (FIXED: uses clipLineToPlate)
// ============================================================
function computeSlits(pA, pB, tol) {
  if(Math.abs(dot(pA.normal, pB.normal)) > 0.3) return null;
  const line = planeIntersectionLine(pA, pB);
  if(!line) return null;
  const { linePoint, lineDir } = line;
  const rA = clipLineToPlate(pA, linePoint, lineDir);
  const rB = clipLineToPlate(pB, linePoint, lineDir);
  if(!rA || !rB) return null;
  const tMin=Math.max(rA[0],rB[0]), tMax=Math.min(rA[1],rB[1]);
  if(tMax-tMin < pA.thick*1.5) return null;
  const slitA = buildSlitOnPlate(pA, pB, linePoint, lineDir, tMin, tMax, tol);
  const slitB = buildSlitOnPlate(pB, pA, linePoint, lineDir, tMin, tMax, tol);
  if(!slitA || !slitB) return null;
  return { slitA, slitB };
}

// ============================================================
// Clip polygon to square plate boundary (Sutherland-Hodgman)
// Returns array of {u,v} points that lie inside [-half, half]²
// ============================================================
function clipPolygonToSquare(pts, half) {
  function clipEdge(input, nx, ny, d) {
    if (input.length === 0) return [];
    const output = [];
    for (let i = 0; i < input.length; i++) {
      const a = input[i], b = input[(i + 1) % input.length];
      const da = nx * a.u + ny * a.v - d;
      const db = nx * b.u + ny * b.v - d;
      if (da <= 0) output.push(a);
      if ((da < 0) !== (db < 0)) {
        const t = da / (da - db);
        output.push({ u: a.u + t * (b.u - a.u), v: a.v + t * (b.v - a.v) });
      }
    }
    return output;
  }
  let p = pts;
  p = clipEdge(p,  1,  0, half);  // u <= +half
  p = clipEdge(p, -1,  0, half);  // u >= -half
  p = clipEdge(p,  0,  1, half);  // v <= +half
  p = clipEdge(p,  0, -1, half);  // v >= -half
  return p;
}

// Build the correct slit polygon in local plate UV coordinates.
//
// Problem with uniform rectangles:
//   The entry side (eu±nx, ev±ny) can protrude outside the plate boundary
//   when the slit direction is not perpendicular to the edge, leaving a
//   region that is not cut and a region that is cut outside the plate.
//
// Fix: extend both long sides well past the entry point (outward), then
//   clip the resulting quad to the plate boundary.  The clipping naturally
//   trims each long side at the exact edge intersection, giving the correct
//   tapered shape where entry-side width == 0 (V at the edge).
//
function slitPolygonLocal(s) {
  const half = s.host.size / 2;
  const eu = s.entry.u, ev = s.entry.v;
  const xu = s.exit.u,  xv = s.exit.v;
  const du = xu - eu,   dv = xv - ev;
  const len = Math.sqrt(du * du + dv * dv);
  if (len < 1e-9) return [];
  const hw = s.width / 2;
  const nx = -dv / len * hw, ny = du / len * hw;  // perp, right side
  // Extend entry side well outside the plate so the clipper can trim it cleanly.
  const ext = half * 3;
  const extu = eu - du / len * ext;
  const extv = ev - dv / len * ext;
  const raw = [
    { u: extu + nx, v: extv + ny },  // A – right, extended past entry
    { u: xu   + nx, v: xv   + ny },  // B – right, at exit (mid-point M)
    { u: xu   - nx, v: xv   - ny },  // C – left,  at exit
    { u: extu - nx, v: extv - ny },  // D – left,  extended past entry
  ];
  return clipPolygonToSquare(raw, half);
}

// ============================================================
// Slit overlap check (2D AABB)
// ============================================================
function slitsOverlap(s1, s2) {
  const exp = Math.max(s1.width, s2.width)/2 + 1e-3;
  const aabb = s => ({
    minU: Math.min(s.entry.u,s.exit.u)-exp, maxU: Math.max(s.entry.u,s.exit.u)+exp,
    minV: Math.min(s.entry.v,s.exit.v)-exp, maxV: Math.max(s.entry.v,s.exit.v)+exp,
  });
  const a=aabb(s1), b=aabb(s2);
  return !(a.maxU<b.minU || b.maxU<a.minU || a.maxV<b.minV || b.maxV<a.minV);
}

// ============================================================
// Main Optimizer — v8b: Random sampling + step optimization
// ============================================================
let PLATES = [];
let slitPairCounter = 0;  // incremented each time a slit pair is committed
let selectedPlateId = null;   // currently selected plate id (null = none)
const plateMeshMap = new Map(); // plateId -> THREE.Mesh (for raycasting)

async function runOptimize() {
  const size     = +document.getElementById('plateSize').value;
  const thick    = +document.getElementById('plateThick').value;
  const radius   = +document.getElementById('targetRadius').value;
  const slitTol  = +document.getElementById('slitTol').value;
  const seed     = +document.getElementById('rngSeed').value;
  const maxPl    = +document.getElementById('maxPlates').value;
  const nRandom  = +document.getElementById('nRandom').value;

  document.getElementById('log').textContent = '';
  slitPairCounter = 0;
  LOG('v8 — ランダムサンプリング + step最適化');
  LOG(`R=${radius} L=${size} thick=${thick} seed=${seed} maxPlates=${maxPl} trials/step=${nRandom}`);

  const rng = makeRng(seed);
  PLATES = [];

  // --- Seed plate ---
  function randOnSphere() {
    const phi=Math.acos(1-2*rng()), th=2*Math.PI*rng();
    return new V3(radius*Math.sin(phi)*Math.cos(th), radius*Math.cos(phi), radius*Math.sin(phi)*Math.sin(th));
  }
  function randTangent(pos) {
    const r=normalize(pos);
    const h=Math.abs(r.y)<0.9?new V3(0,1,0):new V3(1,0,0);
    const t1=normalize(cross(r,h)), t2=normalize(cross(r,t1));
    const a=rng()*2*Math.PI;
    return normalize(add(scale(t1,Math.cos(a)), scale(t2,Math.sin(a))));
  }
  const c0 = randOnSphere();
  PLATES.push(new Plate(0, c0, randTangent(c0), size, thick));
  LOG(`シードプレート: (${c0.x.toFixed(0)},${c0.y.toFixed(0)},${c0.z.toFixed(0)})`);

  // step candidates: multiples of size along intersection line direction
  const STEPS = [];
  for(let i=-1.3; i<=1.31; i+=0.13) if(Math.abs(i)>0.15) STEPS.push(i);

  let stuckCount = 0;
  const t0 = performance.now();

  while(PLATES.length < maxPl) {
    const cands = [];

    // N_RANDOM trials: random (pA, θ) → line-search on step
    for(let trial=0; trial<nRandom; trial++) {
      const pA = PLATES[Math.floor(rng() * PLATES.length)];
      const theta = rng() * 2 * Math.PI;
      const n_B = normalize(add(scale(pA.u, Math.cos(theta)), scale(pA.v, Math.sin(theta))));
      const lineDir = normalize(cross(pA.normal, n_B));

      // Line search: find step that maximizes min-distance to existing plates
      // (= PDS-like uniform sphere coverage)
      let bScore=-Infinity, bResult=null, bCB=null;
      for(const sm of STEPS) {
        const c_B = scale(normalize(add(pA.center, scale(lineDir, sm*size))), radius);
        if(vdist(c_B, pA.center) < size*0.2) continue;  // radial direction → skip

        let minD = Infinity;
        for(const p of PLATES) { const d=vdist(c_B,p.center); if(d<minD) minD=d; }
        if(minD < size*0.2) continue;  // too close to existing

        const pB = new Plate(PLATES.length, c_B, n_B, size, thick);

        // 拘束1: スリット成立（厳密）
        const res = computeSlits(pA, pB, slitTol);
        if(!res) continue;

        // 拘束2: pAの既存スリットと重複なし
        let slitOK=true;
        for(const s of pA.slits) { if(slitsOverlap(s,res.slitA)){slitOK=false;break;} }
        if(!slitOK) continue;

        // 拘束0: pBはpAと物理的に交わること（必要条件）
        if(!obbIntersect(pA.obb(), pB.obb())) continue;

        // 拘束3: 物理干渉なし（pA以外の全プレート）
        let noInter=true;
        for(const p of PLATES) { if(p===pA) continue; if(obbIntersect(p.obb(),pB.obb())){noInter=false;break;} }
        if(!noInter) continue;

        if(minD > bScore) { bScore=minD; bResult=res; bCB=c_B; }
      }
      if(bCB) cands.push({ pA, c_B:bCB, n_B, result:bResult, score:bScore });
    }

    if(cands.length === 0) {
      if(++stuckCount >= 5) { LOG('これ以上追加できません（収束）'); break; }
      continue;
    }
    stuckCount = 0;

    // 最良候補を追加（min距離最大 = 最も孤立した位置 = 球面カバレッジ最大）
    cands.sort((a,b) => b.score-a.score);
    const { pA, c_B, n_B, result } = cands[0];
    const pB = new Plate(PLATES.length, c_B, n_B, size, thick);
    // Assign same pairId to both ends of this slit connection
    const pairId = ++slitPairCounter;
    result.slitA.pairId = pairId;
    result.slitB.pairId = pairId;
    result.slitB.host = pB;  // fix: update host to the actual committed plate object
    pA.slits.push(result.slitA);
    pB.slits.push(result.slitB);
    pA.neighbors.push(pB.id);
    pB.neighbors.push(pA.id);
    PLATES.push(pB);

    // Progress
    const elapsed = ((performance.now()-t0)/1000).toFixed(1);
    LOG(`[${PLATES.length}] (${c_B.x.toFixed(0)},${c_B.y.toFixed(0)},${c_B.z.toFixed(0)}) score=${cands[0].score.toFixed(1)} ${elapsed}s`);
    STAT('st-plates', PLATES.length);
    STAT('st-slits',  PLATES.reduce((a,p)=>a+p.slits.length,0));
    STAT('st-connected', '✓');

    // Render progress every N plates
    if(PLATES.length % 5 === 0 || PLATES.length <= 10) {
      renderScene(PLATES);
    }
    await new Promise(r => setTimeout(r, 0));
  }

  // Final stats
  const totalSlits = PLATES.reduce((a,p)=>a+p.slits.length,0);
  const elapsed = ((performance.now()-t0)/1000).toFixed(1);
  LOG(`\n完了: ${PLATES.length}枚 / ${totalSlits}スリット / ${elapsed}s`);
  STAT('st-plates',    PLATES.length);
  STAT('st-slits',     totalSlits);
  STAT('st-connected', PLATES.length>0?'✓':'—');
  STAT('st-coverage',  computeCoverage(PLATES, radius) + '%');
  renderScene(PLATES);
  // Refresh 2D preview if it's currently visible
  if(typeof updateSVGPreview==='function') updateSVGPreview();
}

// ============================================================
// Sphere coverage estimate (Fibonacci sample points)
// ============================================================
function computeCoverage(plates, radius) {
  if(!plates.length) return 0;
  const N=500, phi=Math.PI*(3-Math.sqrt(5));
  let covered=0;
  for(let i=0;i<N;i++){
    const y=1-(i/(N-1))*2, r=Math.sqrt(Math.max(0,1-y*y));
    const pt = new V3(r*Math.cos(phi*i)*radius, y*radius, r*Math.sin(phi*i)*radius);
    for(const p of plates){
      const loc=p.worldToLocal(pt);
      if(p.inBounds(loc.u, loc.v, 0)){covered++;break;}
    }
  }
  return ((covered/N)*100).toFixed(0);
}

// ============================================================
// Three.js Scene
// ============================================================
let scene, camera, renderer;

function initRenderer() {
  const canvas = document.getElementById('canvas3d');
  renderer = new THREE.WebGLRenderer({ canvas, antialias: true });
  renderer.setPixelRatio(window.devicePixelRatio);
  renderer.setClearColor(0x1a1a2e);
  window.renderer = renderer;

  scene = new THREE.Scene();
  camera = new THREE.PerspectiveCamera(60, canvas.clientWidth/canvas.clientHeight, 1, 20000);
  camera.position.set(0, 200, 800);
  window.camera = camera;

  scene.add(new THREE.AmbientLight(0xffffff, 0.5));
  const dl = new THREE.DirectionalLight(0xffffff, 0.9);
  dl.position.set(1,2,1); scene.add(dl);

  // Orbit controls
  let dragging=false, rightDrag=false, lx=0, ly=0;
  let sph={theta:0.3, phi:1.0, r:800};
  const target=new THREE.Vector3();
  function updateCam(){
    camera.position.set(target.x+sph.r*Math.sin(sph.phi)*Math.sin(sph.theta),target.y+sph.r*Math.cos(sph.phi),target.z+sph.r*Math.sin(sph.phi)*Math.cos(sph.theta));
    camera.lookAt(target);
  }
  updateCam();
  const el=canvas;
  el.addEventListener('mousedown',e=>{dragging=true;rightDrag=(e.button===2);lx=e.clientX;ly=e.clientY;e.preventDefault();});
  el.addEventListener('contextmenu',e=>e.preventDefault());
  window.addEventListener('mouseup',()=>dragging=false);
  window.addEventListener('mousemove',e=>{
    if(!dragging)return;
    const dx=e.clientX-lx,dy=e.clientY-ly;lx=e.clientX;ly=e.clientY;
    if(rightDrag){const right=new THREE.Vector3().crossVectors(camera.getWorldDirection(new THREE.Vector3()),camera.up).normalize();target.addScaledVector(right,-dx*0.5);target.addScaledVector(camera.up,dy*0.5);}
    else{sph.theta-=dx*0.005;sph.phi=Math.max(0.05,Math.min(Math.PI-0.05,sph.phi+dy*0.005));}
    updateCam();
  });
  el.addEventListener('wheel',e=>{sph.r=Math.max(100,sph.r+e.deltaY*0.5);updateCam();});
  let touches=[];
  el.addEventListener('touchstart',e=>{touches=Array.from(e.touches);e.preventDefault();},{passive:false});
  el.addEventListener('touchmove',e=>{
    if(e.touches.length===1){const t=e.touches[0],prev=touches[0];if(prev){sph.theta-=(t.clientX-prev.clientX)*0.005;sph.phi=Math.max(0.05,Math.min(Math.PI-0.05,sph.phi+(t.clientY-prev.clientY)*0.005));}}
    else if(e.touches.length===2){const d0=Math.hypot(touches[0].clientX-touches[1].clientX,touches[0].clientY-touches[1].clientY),d1=Math.hypot(e.touches[0].clientX-e.touches[1].clientX,e.touches[0].clientY-e.touches[1].clientY);sph.r=Math.max(100,sph.r*(d0/d1));}
    touches=Array.from(e.touches);updateCam();e.preventDefault();
  },{passive:false});
  window.addEventListener('resize',()=>{camera.aspect=canvas.clientWidth/canvas.clientHeight;camera.updateProjectionMatrix();renderer.setSize(canvas.clientWidth,canvas.clientHeight,false);});
  renderer.setSize(canvas.clientWidth,canvas.clientHeight,false);
  animate();
  initClickHandler();
}

function animate() { requestAnimationFrame(animate); renderer.render(scene,camera); }

function normalColor(n) {
  const hue=(Math.atan2(n.z,n.x)/(Math.PI*2)+1)%1;
  return new THREE.Color().setHSL(hue,0.7,0.55);
}

function makeBasis(u, v, n) {
  const m = new THREE.Matrix4();
  m.set(u.x,v.x,n.x,0, u.y,v.y,n.y,0, u.z,v.z,n.z,0, 0,0,0,1);
  return m;
}

// Billboard sprite with text drawn on a Canvas texture
function makeTextSprite(text, { color='#ffffff', bgColor=null, fontSize=48, scaleFactor=1 }={}) {
  const canvas = document.createElement('canvas');
  const ctx    = canvas.getContext('2d');
  ctx.font = `bold ${fontSize}px sans-serif`;
  const tw = ctx.measureText(text).width;
  const pad = fontSize * 0.3;
  canvas.width  = Math.ceil(tw + pad * 2);
  canvas.height = Math.ceil(fontSize * 1.4);
  // Re-set font after resize (canvas reset clears state)
  ctx.font = `bold ${fontSize}px sans-serif`;
  if (bgColor) {
    ctx.fillStyle = bgColor;
    ctx.beginPath();
    ctx.roundRect(0, 0, canvas.width, canvas.height, fontSize * 0.2);
    ctx.fill();
  }
  ctx.fillStyle = color;
  ctx.textAlign  = 'center';
  ctx.textBaseline = 'middle';
  ctx.fillText(text, canvas.width / 2, canvas.height / 2);
  const tex = new THREE.CanvasTexture(canvas);
  const mat = new THREE.SpriteMaterial({ map: tex, transparent: true, depthTest: false });
  const sprite = new THREE.Sprite(mat);
  const aspect = canvas.width / canvas.height;
  sprite.scale.set(scaleFactor * aspect, scaleFactor, 1);
  return sprite;
}

function renderScene(plates) {
  while(scene.children.length>2) scene.remove(scene.children[scene.children.length-1]);
  scene.add(new THREE.AxesHelper(80));
  const r = +document.getElementById('targetRadius').value;
  scene.add(new THREE.Mesh(
    new THREE.SphereGeometry(r,32,20),
    new THREE.MeshBasicMaterial({color:0x223344,wireframe:true,transparent:true,opacity:0.08})
  ));

  plateMeshMap.clear();
  const labelScale = plates.length ? plates[0].size * 0.28 : 28;

  // 選択状態の計算
  const hasSelection = selectedPlateId !== null && plates[selectedPlateId] != null;
  const focusSet = new Set(); // 選択プレート + その隣接プレート
  if (hasSelection) {
    focusSet.add(selectedPlateId);
    for (const nId of plates[selectedPlateId].neighbors) focusSet.add(nId);
  }

  plates.forEach((p) => {
    const col = normalColor(p.normal);
    const isDimmed  = hasSelection && !focusSet.has(p.id);
    const isSelected = p.id === selectedPlateId;

    // マテリアル: 非選択時はワイヤーフレームで暗く
    const mat = isDimmed
      ? new THREE.MeshBasicMaterial({color:0x2a2a2a, wireframe:true, transparent:true, opacity:0.3})
      : new THREE.MeshLambertMaterial({
          color: col, transparent: true,
          opacity: isSelected ? 0.90 : 0.72,
          side: THREE.DoubleSide
        });

    const geo  = new THREE.BoxGeometry(p.size, p.size, p.thick);
    const mesh = new THREE.Mesh(geo, mat);
    mesh.position.copy(p.center);
    mesh.quaternion.setFromRotationMatrix(makeBasis(p.u, p.v, p.normal));
    scene.add(mesh);
    plateMeshMap.set(p.id, mesh); // raycasting 用に登録

    if (isDimmed) return; // 暗くしたプレートはラベル・スリット非表示

    // プレート番号ラベル
    const plateLabel = makeTextSprite(String(p.id + 1), {
      color: '#' + col.getHexString(), bgColor: 'rgba(0,0,0,0.55)', scaleFactor: labelScale
    });
    const labelPos = add(p.center, scale(p.normal, p.thick / 2 + labelScale * 0.6));
    plateLabel.position.set(labelPos.x, labelPos.y, labelPos.z);
    scene.add(plateLabel);

    // スリット線 + スリットIDラベル
    p.slits.forEach(s => {
      const ce = slitCutExit(s);
      const wEntry = p.localToWorld(s.entry.u, s.entry.v, 0);
      const wCut   = p.localToWorld(ce.u, ce.v, 0);
      const geo2   = new THREE.BufferGeometry().setFromPoints([
        new THREE.Vector3(wEntry.x, wEntry.y, wEntry.z),
        new THREE.Vector3(wCut.x,   wCut.y,   wCut.z)
      ]);
      scene.add(new THREE.Line(geo2, new THREE.LineBasicMaterial({color:0xffff00, linewidth:2})));

      if (s.pairId != null) {
        const slitLabel = makeTextSprite(String(s.pairId), {
          color: '#e94560', bgColor: 'rgba(0,0,0,0.5)', scaleFactor: labelScale * 0.7
        });
        const sp = p.localToWorld(ce.u, ce.v, p.thick / 2 + labelScale * 0.45);
        slitLabel.position.set(sp.x, sp.y, sp.z);
        scene.add(slitLabel);
      }
    });
  });

  // 接続線: 選択中は選択プレートの接続のみ、非選択時は全接続を表示
  const drawnPairs = new Set();
  plates.forEach(p => {
    if (hasSelection && p.id !== selectedPlateId) return;
    p.neighbors.forEach(neighborId => {
      const key = Math.min(p.id, neighborId) + '_' + Math.max(p.id, neighborId);
      if (drawnPairs.has(key)) return;
      drawnPairs.add(key);
      const other = plates[neighborId];
      if (!other) return;
      const geoConn = new THREE.BufferGeometry().setFromPoints([
        new THREE.Vector3(p.center.x, p.center.y, p.center.z),
        new THREE.Vector3(other.center.x, other.center.y, other.center.z)
      ]);
      scene.add(new THREE.Line(geoConn, new THREE.LineBasicMaterial({color:0xff8800, transparent:true, opacity:0.55})));
    });
  });
}

// ============================================================
// Plate selection (click / tap)
// ============================================================
function selectPlate(plateId) {
  selectedPlateId = plateId;
  renderScene(PLATES);
  updateInfoPanel(plateId);
  // デスクトップ: Info タブへ自動切替
  if (window.innerWidth > 640 && typeof switchTab === 'function') {
    switchTab('info');
  } else {
    // モバイル: 下部パネルを表示
    const panel = document.getElementById('info-panel-mobile');
    if (panel) panel.classList.add('visible');
  }
}

function clearSelection() {
  selectedPlateId = null;
  renderScene(PLATES);
  updateInfoPanel(null);
  const panel = document.getElementById('info-panel-mobile');
  if (panel) panel.classList.remove('visible');
}

function updateInfoPanel(plateId) {
  const desktopEl  = document.getElementById('info-content');
  const mobileTitleEl   = document.getElementById('info-mobile-title');
  const mobileContentEl = document.getElementById('info-mobile-content');

  if (plateId === null || !PLATES.length || !PLATES[plateId]) {
    const empty = '<p style="color:var(--faint);font-size:11px;text-align:center;padding:24px 0 8px;">3Dビューワーのプレートをクリックして選択</p>';
    if (desktopEl)  desktopEl.innerHTML = empty;
    if (mobileTitleEl)   mobileTitleEl.textContent = '—';
    if (mobileContentEl) mobileContentEl.innerHTML = '';
    return;
  }

  const p = PLATES[plateId];
  const title = `Plate ${p.id + 1}`;
  let rows = '';
  if (p.slits.length === 0) {
    rows = '<p style="color:var(--faint);font-size:11px;">接続なし</p>';
  } else {
    p.slits.forEach(s => {
      rows += `<div class="slit-row" onclick="selectPlate(${s.inserted.id})">
        <span class="slit-id">Slit ${s.pairId}</span>
        <span class="slit-dest">→ Plate ${s.inserted.id + 1}</span>
      </div>`;
    });
  }
  const html = `
    <div style="font-size:11px;color:var(--muted);margin-bottom:10px;">
      スリット数: <strong style="color:var(--text)">${p.slits.length}</strong>本
    </div>${rows}`;

  if (desktopEl)  desktopEl.innerHTML = `<div style="margin-bottom:12px;font-size:15px;font-weight:700;color:var(--accent)">${title}</div>${html}`;
  if (mobileTitleEl)   mobileTitleEl.textContent = title;
  if (mobileContentEl) mobileContentEl.innerHTML = html;
}

function initClickHandler() {
  const canvas    = document.getElementById('canvas3d');
  const raycaster = new THREE.Raycaster();
  const mouse     = new THREE.Vector2();
  let dragStart   = null;

  // マウス: ドラッグと区別するため mousedown 位置を記録
  canvas.addEventListener('mousedown', e => { dragStart = {x: e.clientX, y: e.clientY}; });
  canvas.addEventListener('click', e => {
    if (dragStart && Math.hypot(e.clientX - dragStart.x, e.clientY - dragStart.y) > 5) {
      dragStart = null; return; // ドラッグなのでスキップ
    }
    dragStart = null;
    const rect = canvas.getBoundingClientRect();
    mouse.x =  ((e.clientX - rect.left) / canvas.clientWidth)  * 2 - 1;
    mouse.y = -((e.clientY - rect.top)  / canvas.clientHeight) * 2 + 1;
    raycaster.setFromCamera(mouse, camera);
    const hits = raycaster.intersectObjects([...plateMeshMap.values()]);
    if (hits.length) {
      for (const [id, m] of plateMeshMap) {
        if (m === hits[0].object) {
          selectedPlateId === id ? clearSelection() : selectPlate(id);
          break;
        }
      }
    } else {
      clearSelection();
    }
  });

  // タッチ: タップと区別するため touchstart 位置を記録
  let touchStart = null;
  canvas.addEventListener('touchstart', e => {
    touchStart = e.touches.length === 1 ? {x: e.touches[0].clientX, y: e.touches[0].clientY} : null;
  }, {passive: true});
  canvas.addEventListener('touchend', e => {
    if (!touchStart || e.changedTouches.length !== 1) return;
    const t = e.changedTouches[0];
    if (Math.hypot(t.clientX - touchStart.x, t.clientY - touchStart.y) > 12) return;
    touchStart = null;
    const rect = canvas.getBoundingClientRect();
    mouse.x =  ((t.clientX - rect.left) / canvas.clientWidth)  * 2 - 1;
    mouse.y = -((t.clientY - rect.top)  / canvas.clientHeight) * 2 + 1;
    raycaster.setFromCamera(mouse, camera);
    const hits = raycaster.intersectObjects([...plateMeshMap.values()]);
    if (hits.length) {
      for (const [id, m] of plateMeshMap) {
        if (m === hits[0].object) {
          selectedPlateId === id ? clearSelection() : selectPlate(id);
          break;
        }
      }
    } else {
      clearSelection();
    }
  }, {passive: true});
}

// ============================================================
// Exports: CSV, DXF, PNG
// ============================================================
function exportCSV() {
  if(!PLATES.length){alert('Run optimization first');return;}
  const rows=['id,cx,cy,cz,nx,ny,nz,num_slits'];
  PLATES.forEach((p,i)=>{rows.push([i,p.center.x.toFixed(2),p.center.y.toFixed(2),p.center.z.toFixed(2),p.normal.x.toFixed(4),p.normal.y.toFixed(4),p.normal.z.toFixed(4),p.slits.length].join(','));});
  rows.push('','plate_id,slit_idx,other_id,entry_u,entry_v,exit_u,exit_v,width');
  PLATES.forEach((p,i)=>{p.slits.forEach((s,si)=>{rows.push([i,si,s.inserted.id,s.entry.u.toFixed(2),s.entry.v.toFixed(2),s.exit.u.toFixed(2),s.exit.v.toFixed(2),s.width.toFixed(3)].join(','));});});
  download('slit_plates.csv',rows.join('\n'),'text/csv');
}

// Helper: slit label position (beside the slit, clamped inside plate)
function slitLabelPos(s, cx, cy, size) {
  const mx=(s.entry.u+s.exit.u)/2, mv=(s.entry.v+s.exit.v)/2;
  const du=s.exit.u-s.entry.u, dv=s.exit.v-s.entry.v;
  const sl=Math.sqrt(du*du+dv*dv);
  const nx=sl>1e-6?-dv/sl:1, ny=sl>1e-6?du/sl:0;
  const off=size*0.07;
  const h=size/2-size*0.1;
  const lx=Math.max(-h,Math.min(h,mx+nx*off));
  const ly=Math.max(-h,Math.min(h,mv+ny*off));
  return {x:lx+cx, y:ly+cy};
}

function exportDXF() {
  if(!PLATES.length){alert('Run optimization first');return;}
  const cols=+document.getElementById('dxfCols').value, spacing=+document.getElementById('dxfSpacing').value, size=PLATES[0].size;
  const sorted=[...PLATES].sort((a,b)=>a.id-b.id);
  let body='';
  sorted.forEach((p,idx)=>{
    const ox=(idx%cols)*(size+spacing), oy=-Math.floor(idx/cols)*(size+spacing), h=size/2;
    body+=dxfRect(ox-h,oy-h,ox+h,oy+h,'PLATES');
    body+=dxfText(ox-h+2,oy+h-size*0.1,String(p.id+1),'LABELS',size*0.08);
    p.slits.forEach(s=>{
      // Use clipped polygon: long sides extended past entry, then trimmed to plate boundary.
      // This ensures no overshoot outside the plate and correct taper at the edge.
      const poly=slitPolygonLocal(s);
      if(poly.length<3)return;
      for(let i=0;i<poly.length;i++){
        const a=poly[i],b=poly[(i+1)%poly.length];
        body+=dxfLine(a.u+ox,a.v+oy,b.u+ox,b.v+oy,'SLITS');
      }
      if(s.pairId!=null){
        const lp=slitLabelPos(s,ox,oy,size);
        body+=dxfText(lp.x,lp.y,String(s.pairId),'SLIT_IDS',size*0.065);
      }
    });
  });
  const full='0\nSECTION\n2\nHEADER\n9\n$INSUNITS\n70\n4\n0\nENDSEC\n0\nSECTION\n2\nENTITIES\n'+body+'0\nENDSEC\n0\nEOF\n';
  download('slit_plates.dxf',full,'application/dxf');
}

function buildSVGString() {
  if(!PLATES.length) return '<svg xmlns="http://www.w3.org/2000/svg"><text x="10" y="20" font-size="14" fill="#999">No plates yet — run Optimize first</text></svg>';
  const cols=+document.getElementById('dxfCols').value, spacing=+document.getElementById('dxfSpacing').value, size=PLATES[0].size;
  const sorted=[...PLATES].sort((a,b)=>a.id-b.id);
  const numRows=Math.ceil(sorted.length/cols);
  const pad=spacing/2;
  const W=cols*(size+spacing)+spacing, H=numRows*(size+spacing)+spacing;
  const fs_label=(size*0.08).toFixed(2), fs_id=(size*0.065).toFixed(2);

  let s=`<svg xmlns="http://www.w3.org/2000/svg" width="${W}" height="${H}" viewBox="0 0 ${W} ${H}">\n`;
  s+=`<rect width="100%" height="100%" fill="#fff"/>\n`;
  s+=`<style>.plate{fill:#f8f8f8;stroke:#333;stroke-width:0.5}.lbl{font:bold ${fs_label}px sans-serif;fill:#555}.slit{fill:#333}.sid{font:bold ${fs_id}px sans-serif;fill:#c0392b}</style>\n`;

  sorted.forEach((p,idx)=>{
    const cx=pad+(idx%cols)*(size+spacing)+size/2;
    const cy=pad+Math.floor(idx/cols)*(size+spacing)+size/2;
    const h=size/2;
    s+=`<rect class="plate" x="${cx-h}" y="${cy-h}" width="${size}" height="${size}"/>\n`;
    s+=`<text class="lbl" x="${(cx-h+2).toFixed(1)}" y="${(cy-h+size*0.09).toFixed(1)}">${p.id+1}</text>\n`;
    p.slits.forEach(sl=>{
      // Clip slit polygon to plate boundary for correct cut path
      const poly=slitPolygonLocal(sl);
      if(poly.length<3)return;
      const pts=poly.map(pt=>`${(pt.u+cx).toFixed(2)},${(pt.v+cy).toFixed(2)}`).join(' ');
      s+=`<polygon class="slit" points="${pts}"/>\n`;
      if(sl.pairId!=null){
        const lp=slitLabelPos(sl,cx,cy,size);
        s+=`<text class="sid" x="${lp.x.toFixed(2)}" y="${lp.y.toFixed(2)}">${sl.pairId}</text>\n`;
      }
    });
  });
  s+='</svg>\n';
  return s;
}

function exportSVG() {
  if(!PLATES.length){alert('Run optimization first');return;}
  download('slit_plates.svg', buildSVGString(), 'image/svg+xml');
}

function dxfRect(x1,y1,x2,y2,l){return dxfLine(x1,y1,x2,y1,l)+dxfLine(x2,y1,x2,y2,l)+dxfLine(x2,y2,x1,y2,l)+dxfLine(x1,y2,x1,y1,l);}
function dxfLine(x1,y1,x2,y2,l){return `0\nLINE\n8\n${l}\n10\n${x1.toFixed(4)}\n20\n${y1.toFixed(4)}\n30\n0\n11\n${x2.toFixed(4)}\n21\n${y2.toFixed(4)}\n31\n0\n`;}
function dxfText(x,y,t,l,h){return `0\nTEXT\n8\n${l}\n10\n${x.toFixed(4)}\n20\n${y.toFixed(4)}\n30\n0\n40\n${h.toFixed(4)}\n1\n${t}\n`;}

function exportTopView() {
  if(!PLATES.length){alert('Run optimization first');return;}
  const sc=+document.getElementById('topScale').value, size=PLATES[0].size;
  const r=+document.getElementById('targetRadius').value, dim=Math.ceil((r*2+size)*sc*1.15);
  const canvas=document.getElementById('topview-canvas');
  canvas.width=canvas.height=dim;
  const ctx=canvas.getContext('2d');
  ctx.fillStyle='#1a1a2e';ctx.fillRect(0,0,dim,dim);
  const cx=dim/2,cy=dim/2;
  PLATES.forEach((p,i)=>{
    const x=cx+p.center.x*sc,y=cy-p.center.z*sc,h=size*sc/2;
    const c=normalColor(p.normal);
    ctx.fillStyle=`rgba(${~~(c.r*255)},${~~(c.g*255)},${~~(c.b*255)},0.6)`;
    ctx.strokeStyle=`rgb(${~~(c.r*255)},${~~(c.g*255)},${~~(c.b*255)})`;
    ctx.lineWidth=1;ctx.fillRect(x-h,y-h,h*2,h*2);ctx.strokeRect(x-h,y-h,h*2,h*2);
    ctx.fillStyle='#fff';ctx.font=`${Math.max(8,h*0.4)}px monospace`;ctx.textAlign='center';ctx.textBaseline='middle';
    ctx.fillText(String(i+1),x,y);
  });
  canvas.toBlob(blob=>{const url=URL.createObjectURL(blob);const a=document.createElement('a');a.href=url;a.download='slit_topview.png';a.click();URL.revokeObjectURL(url);});
}

function download(name, content, mime) {
  const blob=new Blob([content],{type:mime});const a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download=name;a.click();
}

function toggleSidebar() {
  const sb=document.getElementById('sidebar'), cv=document.getElementById('canvas3d'), btn=document.getElementById('toggle-btn');
  const collapsed=sb.classList.toggle('collapsed');
  btn.textContent=collapsed?'▶':'◀';
  setTimeout(()=>{camera.aspect=cv.clientWidth/cv.clientHeight;camera.updateProjectionMatrix();renderer.setSize(cv.clientWidth,cv.clientHeight,false);},260);
}

initRenderer();
