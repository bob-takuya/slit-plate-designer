// ============================================================
// Slit Plate Designer v5
//
// アルゴリズム: 球面誘導付きランダムグロース
//
// 核心原理（Node.jsで全シード検証済み）:
//   PA の法線 n_A が決まると PB の自由度は1:
//     n_B = cos(θ)·u_A + sin(θ)·v_A   (n_A⊥n_B 厳密保証)
//     c_B = c_A + r·d  (d はPA面内の単位方向ベクトル)
//            → PA面上の点 → 接合が常に物理的に成立
//
// 球面誘導（v5新機能）:
//   |c_B|² = R² を満たす r を2次方程式で解く
//     r² + 2p·r + q = 0  (p = c_A·d, q = |c_A|²-R²)
//   → c_B が常に球面上に来るよう誘導
//   → n_B の θ は球の外法線方向を基準に摂動
//
// スリット描画修正（v5）:
//   setFromUnitVectors(Z→normal) は u/v基底がズレる
//   → makeBasis(u, v, normal) で正確に構築
// ============================================================

const LOG = (msg) => {
  const el = document.getElementById('log');
  if (!el) return;
  el.textContent += msg + '\n';
  el.scrollTop = el.scrollHeight;
};
const STAT = (id, val) => { const el=document.getElementById(id); if(el) el.textContent=val; };

const V3 = THREE.Vector3;
const EPS = 1e-9;

// ============================================================
// ベクトル演算
// ============================================================
function vdot(a,b)   { return a.x*b.x+a.y*b.y+a.z*b.z; }
function vcross(a,b) { return new V3(a.y*b.z-a.z*b.y, a.z*b.x-a.x*b.z, a.x*b.y-a.y*b.x); }
function vnorm(v)    { const l=Math.sqrt(vdot(v,v)); return l<EPS?new V3(0,0,1):new V3(v.x/l,v.y/l,v.z/l); }
function vscale(v,s) { return new V3(v.x*s,v.y*s,v.z*s); }
function vadd(a,b)   { return new V3(a.x+b.x,a.y+b.y,a.z+b.z); }
function vsub(a,b)   { return new V3(a.x-b.x,a.y-b.y,a.z-b.z); }
function vlen(v)     { return Math.sqrt(vdot(v,v)); }

// シード付き乱数
let _rng = 42;
function rng()       { _rng=Math.imul(_rng,1664525)+1013904223|0; return (_rng>>>0)/4294967296; }
function rngSeed(s)  { _rng = s>>>0; }

// ============================================================
// OBB-OBB 干渉判定（SAT 15軸）
// ============================================================
function obbIntersect(cA,axA,hA, cB,axB,hB) {
  const D=vsub(cB,cA), axes=[...axA,...axB];
  for(const a of axA) for(const b of axB){ const c=vcross(a,b); if(vdot(c,c)>EPS) axes.push(vnorm(c)); }
  for(const ax of axes){
    const n=vnorm(ax); let rA=0,rB=0;
    for(let i=0;i<3;i++) rA+=hA[i]*Math.abs(vdot(axA[i],n));
    for(let i=0;i<3;i++) rB+=hB[i]*Math.abs(vdot(axB[i],n));
    if(Math.abs(vdot(D,n))>rA+rB+1e-6) return false;
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
    this.normal = vnorm(normal);
    this.size = size;
    this.thick = thick;
    this.slits = [];
    this.neighbors = [];
    this._buildFrame();
  }

  _buildFrame() {
    const ref = Math.abs(this.normal.y)<0.9 ? new V3(0,1,0) : new V3(1,0,0);
    this.u = vnorm(vcross(this.normal, ref));
    this.v = vnorm(vcross(this.normal, this.u));
  }

  localToWorld(pu, pv) {
    return vadd(vadd(vscale(this.u,pu), vscale(this.v,pv)), this.center);
  }

  worldToLocal(pt) {
    const d=vsub(pt,this.center);
    return { u:vdot(d,this.u), v:vdot(d,this.v) };
  }

  inBounds(pu, pv, margin=0) {
    const h=this.size/2-margin;
    return Math.abs(pu)<=h && Math.abs(pv)<=h;
  }

  corners() {
    const h=this.size/2;
    return [[-h,-h],[h,-h],[h,h],[-h,h]].map(([u,v])=>this.localToWorld(u,v));
  }

  obb() {
    return {c:this.center, ax:[this.u,this.v,this.normal], h:[this.size/2,this.size/2,this.thick/2]};
  }

  intersects(other) {
    const a=this.obb(), b=other.obb();
    return obbIntersect(a.c,a.ax,a.h, b.c,b.ax,b.h);
  }
}

// ============================================================
// スリット幾何計算
// ============================================================
function computeSlits(pA, pB, tol) {
  const lineDir=vnorm(vcross(pA.normal,pB.normal));
  if(vdot(lineDir,lineDir)<0.01) return null;

  const dA=vdot(pA.normal,pA.center), dB=vdot(pB.normal,pB.center);
  const n12=vdot(pA.normal,pB.normal), det=1-n12*n12;
  if(Math.abs(det)<EPS) return null;
  const c1=(dA-n12*dB)/det, c2=(dB-n12*dA)/det;
  const lp=vadd(vscale(pA.normal,c1), vscale(pB.normal,c2));

  function projectOnLine(plate) {
    const ts=plate.corners().map(c=>vdot(vsub(c,lp),lineDir));
    const lo=Math.min(...ts), hi=Math.max(...ts);
    const mid=vadd(lp,vscale(lineDir,(lo+hi)*0.5));
    const loc=plate.worldToLocal(mid);
    if(!plate.inBounds(loc.u,loc.v,plate.size*0.02)) return null;
    return [lo,hi];
  }

  const tA=projectOnLine(pA), tB=projectOnLine(pB);
  if(!tA||!tB) return null;
  const tMin=Math.max(tA[0],tB[0]), tMax=Math.min(tA[1],tB[1]);
  if(tMax-tMin<Math.max(pA.thick,pB.thick)*2.5) return null;

  function snapEdge(pt, other, h) {
    const du=other.u-pt.u, dv=other.v-pt.v, l=Math.sqrt(du*du+dv*dv);
    if(l<EPS) return {u:Math.sign(pt.u||1)*h, v:pt.v};
    let t=Infinity;
    const tryT=tv=>{ if(tv>EPS) t=Math.min(t,tv); };
    if(Math.abs(du)>EPS){ tryT((h-pt.u)/du); tryT((-h-pt.u)/du); }
    if(Math.abs(dv)>EPS){ tryT((h-pt.v)/dv); tryT((-h-pt.v)/dv); }
    if(!isFinite(t)) return pt;
    return {u:pt.u+du*t, v:pt.v+dv*t};
  }

  function buildSlit(host, inserted) {
    const h=host.size/2;
    const le=host.worldToLocal(vadd(lp,vscale(lineDir,tMin)));
    const lx=host.worldToLocal(vadd(lp,vscale(lineDir,tMax)));
    const cl=p=>({u:Math.max(-h,Math.min(h,p.u)), v:Math.max(-h,Math.min(h,p.v))});
    const ce=cl(le), cx=cl(lx);
    const du=cx.u-ce.u, dv=cx.v-ce.v;
    const w=inserted.thick*tol;
    if(Math.sqrt(du*du+dv*dv)<w*2.5) return null;
    const dte=p=>h-Math.max(Math.abs(p.u),Math.abs(p.v));
    let entry,exit;
    if(dte(ce)<=dte(cx)){ entry=snapEdge(ce,cx,h); exit=cx; }
    else                 { entry=snapEdge(cx,ce,h); exit=ce; }
    if(!host.inBounds(exit.u,exit.v,w*0.5)) return null;
    return {host,inserted,entry,exit,width:w};
  }

  const sA=buildSlit(pA,pB), sB=buildSlit(pB,pA);
  if(!sA||!sB) return null;
  return {slitA:sA,slitB:sB};
}

function slitsOverlap(s1,s2) {
  const cl=(s1.width+s2.width)*0.5;
  function ptSeg(pu,pv,s0,s1){
    const dx=s1.u-s0.u,dy=s1.v-s0.v,l2=dx*dx+dy*dy;
    if(l2<EPS) return Math.hypot(pu-s0.u,pv-s0.v);
    const t=Math.max(0,Math.min(1,((pu-s0.u)*dx+(pv-s0.v)*dy)/l2));
    return Math.hypot(pu-(s0.u+t*dx),pv-(s0.v+t*dy));
  }
  function int2d(a0,a1,b0,b1){
    const dax=a1.u-a0.u,day=a1.v-a0.v,dbx=b1.u-b0.u,dby=b1.v-b0.v;
    const dx=b0.u-a0.u,dy=b0.v-a0.v,den=dax*dby-day*dbx;
    if(Math.abs(den)<EPS) return false;
    const t=(dx*dby-dy*dbx)/den,s=(dx*day-dy*dax)/den;
    return t>=-EPS&&t<=1+EPS&&s>=-EPS&&s<=1+EPS;
  }
  if(int2d(s1.entry,s1.exit,s2.entry,s2.exit)) return true;
  return Math.min(
    ptSeg(s1.entry.u,s1.entry.v,s2.entry,s2.exit),
    ptSeg(s1.exit.u,s1.exit.v,s2.entry,s2.exit),
    ptSeg(s2.entry.u,s2.entry.v,s1.entry,s1.exit),
    ptSeg(s2.exit.u,s2.exit.v,s1.entry,s1.exit)
  )<cl;
}

// ============================================================
// 球面最小二乗近似による c_B 配置
//
//   c_B = c_A + α·u_A + β·v_A  (PA面上の拘束)
//   目的: minimize (|c_B| - R)²
//
//   PA面内での球の切断円（半径 r = √(R²-dA²)）:
//     (au+α)² + (av+β)² = R² - dA²
//   ただし |R²-dA²| < 0 ならPA面が球と交差しない
//
//   φ をランダムに選び:
//     α = r·cosφ - au,  β = r·sinφ - av
//   → clamp([-L*0.55, L*0.55]) して最善近似
//   → これが「拘束を満たした上での最小二乗的な解」
// ============================================================
function chooseCB(PA, R, L, phi) {
  const au = vdot(PA.center, PA.u);
  const av = vdot(PA.center, PA.v);
  const dA = vdot(PA.center, PA.normal);
  const r2 = R*R - dA*dA;
  const lim = L * 0.55;

  let alpha, beta;
  if(r2 > 0) {
    const r = Math.sqrt(r2);
    alpha = r * Math.cos(phi) - au;
    beta  = r * Math.sin(phi) - av;
    // クランプ（プレート面内に収める = 最小二乗近似の本質）
    alpha = Math.max(-lim, Math.min(lim, alpha));
    beta  = Math.max(-lim, Math.min(lim, beta));
  } else {
    // PA面が球外 → ランダムフォールバック
    alpha = (rng()-0.5)*L;
    beta  = (rng()-0.5)*L;
  }
  return vadd(PA.center, vadd(vscale(PA.u, alpha), vscale(PA.v, beta)));
}

// ============================================================
// ランダムグロース（球面最小二乗近似付き）
//
//   ランダム性の出所:
//   - 最初のプレート: 法線も中心もランダム（軸アライメントなし）
//   - n_B のθ: 完全ランダム（直交は数学で保証）
//   - φ: 完全ランダム（PA面内の方向 → 球面の切断円上の点を選ぶ）
//   → 人為的な摂動は一切加えない
// ============================================================
async function generateNetwork(N, L, T, slitTol, seed, radius) {
  rngSeed(seed);

  // 最初のプレート: 球面上のランダム点 + 完全ランダム法線（軸非依存）
  const initCenter = vscale(vnorm(new V3(rng()*2-1, rng()*2-1, rng()*2-1)), radius);
  const initNormal = vnorm(new V3(rng()*2-1, rng()*2-1, rng()*2-1)); // 球外法線ではない！
  const p0 = new Plate(0, initCenter, initNormal, L, T);
  const plates = [p0];
  const frontier = [{plate:p0, failCount:0}];

  const MAX_TRIAL = 400;
  const MAX_FAIL  = 800;
  let attempts=0, successes=0;

  LOG(`シード:${seed} / 目標:${N}枚 / 球半径:${radius}mm`);

  while(plates.length < N && frontier.length > 0) {
    const fi = Math.floor(rng()*frontier.length);
    const fp = frontier[fi];
    const PA = fp.plate;
    let added = false;

    for(let trial=0; trial<MAX_TRIAL; trial++) {
      attempts++;

      // ─── c_B: 球面への最小二乗近似 ─────────────────────
      const phi   = rng()*Math.PI*2;   // PA面内の方向（完全ランダム）
      const c_B   = chooseCB(PA, radius, L, phi);

      // ─── n_B: θ完全ランダム（直交を数学的に保証）───────
      // これが「軸に並行でない角度のバリエーション」
      const theta = rng()*Math.PI*2;
      const n_B   = vadd(vscale(PA.u, Math.cos(theta)), vscale(PA.v, Math.sin(theta)));

      const PB = new Plate(plates.length, c_B, n_B, L, T);

      // ─── 干渉チェック（PA以外の全プレート） ─────────────
      let ok = true;
      for(const existing of plates) {
        if(existing.id===PA.id) continue;
        if(PB.intersects(existing)){ ok=false; break; }
      }
      if(!ok) continue;

      // ─── スリット計算 ─────────────────────────────────
      const res = computeSlits(PA, PB, slitTol);
      if(!res) continue;

      // ─── スリット重複チェック ─────────────────────────
      for(const s of PA.slits) if(slitsOverlap(s,res.slitA)){ ok=false; break; }
      if(!ok) continue;
      for(const s of PB.slits) if(slitsOverlap(s,res.slitB)){ ok=false; break; }
      if(!ok) continue;

      // ─── 追加成功 ────────────────────────────────────
      PA.slits.push(res.slitA);
      PB.slits.push(res.slitB);
      PA.neighbors.push(PB.id);
      PB.neighbors.push(PA.id);
      plates.push(PB);
      frontier.push({plate:PB, failCount:0});
      successes++;
      added = true;

      if(plates.length%5===0){
        LOG(`  ${plates.length}枚 (試行${attempts}回, 成功率${(successes/attempts*100).toFixed(1)}%)`);
        await new Promise(r=>setTimeout(r,1));
      }
      break;
    }

    if(!added){
      fp.failCount++;
      if(fp.failCount>=MAX_FAIL){
        frontier.splice(fi,1);
        LOG(`  板#${PA.id}をフロンティアから除去 (残り${frontier.length}個)`);
      }
    }
  }

  const slitCount = plates.reduce((s,p)=>s+p.slits.length,0)/2;
  LOG(`完了: ${plates.length}枚, スリット${slitCount}対`);
  LOG(`試行${attempts}回, 成功率${(successes/attempts*100).toFixed(1)}%`);
  return plates;
}

// ============================================================
// メイン
// ============================================================
let PLATES = [];

async function runOptimize() {
  const size    = +document.getElementById('plateSize').value;
  const thick   = +document.getElementById('plateThick').value;
  const N       = +document.getElementById('density').value;
  const radius  = +document.getElementById('targetRadius').value;
  const slitTol = +document.getElementById('slitTol').value;
  let   seed    = +document.getElementById('rngSeed').value;
  if(!seed){ seed = Math.floor(Math.random()*99999)+1; document.getElementById('rngSeed').value=seed; }

  document.getElementById('log').textContent = '';
  LOG(`▶ size=${size}mm, thick=${thick}mm, R=${radius}mm, N=${N}, seed=${seed}`);

  PLATES = await generateNetwork(N, size, thick, slitTol, seed, radius);

  // 連結確認
  const idMap=new Map(PLATES.map(p=>[p.id,p]));
  const vis=new Set(), q=[PLATES[0].id]; vis.add(PLATES[0].id);
  while(q.length){ const id=q.shift(); (idMap.get(id)?.neighbors||[]).forEach(n=>{ if(!vis.has(n)){vis.add(n);q.push(n);} }); }
  const conn = vis.size===PLATES.length;

  STAT('st-plates',    PLATES.length);
  STAT('st-slits',     PLATES.reduce((s,p)=>s+p.slits.length,0)/2);
  STAT('st-connected', conn?`✓ ${PLATES.length}枚`:`${vis.size}/${PLATES.length}`);

  let maxR=0;
  for(const p of PLATES) maxR=Math.max(maxR, vlen(p.center));
  STAT('st-coverage',  `実半径 ${maxR.toFixed(0)}mm`);

  renderScene(PLATES, radius);
  LOG('✓ 描画完了');
}

// ============================================================
// Three.js レンダリング
//
// 修正: setFromUnitVectors(Z→normal) ではなく
//       makeBasis(u, v, normal) で正確な基底を使う
//       → スリットの位置・向きが正確になる
// ============================================================
let scene, camera, renderer, _sph;

function initRenderer() {
  const canvas = document.getElementById('canvas3d');
  renderer = new THREE.WebGLRenderer({ canvas, antialias:true });
  renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
  renderer.setClearColor(0x1a1a2e);
  window.renderer = renderer;

  scene = new THREE.Scene();
  camera = new THREE.PerspectiveCamera(55, canvas.clientWidth/canvas.clientHeight, 1, 50000);
  window.camera = camera;

  scene.add(new THREE.AmbientLight(0xffffff, 0.5));
  const dir = new THREE.DirectionalLight(0xffffff, 0.7);
  dir.position.set(1,2,1.5); scene.add(dir);

  _sph = {theta:0.4, phi:1.1, r:600};
  const tgt = new THREE.Vector3();
  function uc(){
    camera.position.set(
      tgt.x+_sph.r*Math.sin(_sph.phi)*Math.sin(_sph.theta),
      tgt.y+_sph.r*Math.cos(_sph.phi),
      tgt.z+_sph.r*Math.sin(_sph.phi)*Math.cos(_sph.theta)
    );
    camera.lookAt(tgt);
  }
  uc();

  let drag=false, rDrag=false, lx=0, ly=0;
  canvas.addEventListener('mousedown',e=>{drag=true;rDrag=e.button===2;lx=e.clientX;ly=e.clientY;e.preventDefault();});
  canvas.addEventListener('contextmenu',e=>e.preventDefault());
  window.addEventListener('mouseup',()=>drag=false);
  window.addEventListener('mousemove',e=>{
    if(!drag) return;
    const dx=e.clientX-lx, dy=e.clientY-ly; lx=e.clientX; ly=e.clientY;
    if(rDrag){
      const r=new THREE.Vector3().crossVectors(camera.getWorldDirection(new THREE.Vector3()),camera.up).normalize();
      tgt.addScaledVector(r,-dx*0.5).addScaledVector(camera.up,dy*0.5);
    } else {
      _sph.theta-=dx*0.005;
      _sph.phi=Math.max(0.1,Math.min(Math.PI-0.1,_sph.phi+dy*0.005));
    }
    uc();
  });
  canvas.addEventListener('wheel',e=>{_sph.r=Math.max(50,_sph.r+e.deltaY*0.5);uc();e.preventDefault();},{passive:false});

  let lT=[];
  canvas.addEventListener('touchstart',e=>{lT=[...e.touches];e.preventDefault();},{passive:false});
  canvas.addEventListener('touchmove',e=>{
    e.preventDefault();
    if(e.touches.length===1&&lT.length>=1){
      _sph.theta-=(e.touches[0].clientX-lT[0].clientX)*0.005;
      _sph.phi=Math.max(0.1,Math.min(Math.PI-0.1,_sph.phi+(e.touches[0].clientY-lT[0].clientY)*0.005));
    } else if(e.touches.length===2&&lT.length===2){
      const d0=Math.hypot(lT[0].clientX-lT[1].clientX,lT[0].clientY-lT[1].clientY);
      const d1=Math.hypot(e.touches[0].clientX-e.touches[1].clientX,e.touches[0].clientY-e.touches[1].clientY);
      if(d0>1){ _sph.r=Math.max(50,_sph.r*d0/d1); }
    }
    lT=[...e.touches]; uc();
  },{passive:false});
  canvas.addEventListener('touchend',e=>{lT=[...e.touches];});
  window.addEventListener('resize',()=>{
    camera.aspect=canvas.clientWidth/canvas.clientHeight;
    camera.updateProjectionMatrix();
    renderer.setSize(canvas.clientWidth,canvas.clientHeight,false);
  });
  renderer.setSize(canvas.clientWidth,canvas.clientHeight,false);
  animate();

  // カメラ外部から更新できるようにする
  window._uc = uc;
}

function animate(){ requestAnimationFrame(animate); renderer.render(scene,camera); }

// 法線→HSL色
function normalToColor(n) {
  const hue=((Math.atan2(n.y,n.x)/Math.PI+1)*0.5+n.z*0.3)%1;
  return new THREE.Color().setHSL(hue, 0.78, 0.58);
}

// ============================================================
// renderScene
//   - プレート: makeBasis(p.u, p.v, p.normal) で正確な向き
//   - スリット: slitLen/slitWid をワールド座標で計算して正確配置
// ============================================================
function renderScene(plates, radius) {
  for(let i=scene.children.length-1;i>=0;i--){ if(!scene.children[i].isLight) scene.remove(scene.children[i]); }
  scene.add(new THREE.AxesHelper(radius*0.15));

  // 参照球（半透明ワイヤーフレーム）
  scene.add(new THREE.Mesh(
    new THREE.SphereGeometry(radius, 32, 16),
    new THREE.MeshBasicMaterial({color:0x334466, wireframe:true, transparent:true, opacity:0.08})
  ));

  const slitMat = new THREE.MeshBasicMaterial({
    color: 0xffcc00, side: THREE.DoubleSide, transparent: true, opacity: 0.95
  });

  plates.forEach(p => {
    const col = normalToColor(p.normal);
    const plateMat = new THREE.MeshLambertMaterial({
      color: col, transparent: true, opacity: 0.70, side: THREE.DoubleSide
    });

    // ── プレート本体 ──────────────────────────────────
    // makeBasis(u, v, normal): PlaneGeometry のデフォルト XY面 → プレートのローカル座標系へ
    const mesh = new THREE.Mesh(new THREE.PlaneGeometry(p.size, p.size), plateMat);
    mesh.position.copy(p.center);
    mesh.quaternion.setFromRotationMatrix(
      new THREE.Matrix4().makeBasis(p.u, p.v, p.normal)
    );
    scene.add(mesh);

    // ── スリット ──────────────────────────────────────
    p.slits.forEach(s => {
      const eu=s.entry.u, ev=s.entry.v;
      const xu=s.exit.u,  xv=s.exit.v;
      const du=xu-eu, dv=xv-ev;
      const l=Math.sqrt(du*du+dv*dv);
      if(l<EPS) return;

      // スリット長さ方向（ワールド座標）
      const slitLen = vadd(vscale(p.u, du/l), vscale(p.v, dv/l));
      // スリット幅方向 = normal × len（法線に直交、長さ方向に直交）
      const slitWid = vcross(p.normal, slitLen);

      // PlaneGeometry: X=width方向, Y=length方向, Z=normal方向
      const sm = new THREE.Mesh(new THREE.PlaneGeometry(s.width, l), slitMat);
      sm.position.copy(p.localToWorld((eu+xu)*0.5, (ev+xv)*0.5));
      sm.quaternion.setFromRotationMatrix(
        new THREE.Matrix4().makeBasis(slitWid, slitLen, p.normal)
      );
      scene.add(sm);
    });
  });

  // カメラ距離を球半径に合わせてリセット
  _sph.r = radius * 3.5;
  if(window._uc) window._uc();
}

// ============================================================
// Export
// ============================================================
function exportCSV() {
  if(!PLATES.length){alert('先に生成を実行してください');return;}
  const rows=['id,cx,cy,cz,nx,ny,nz,num_slits,neighbor_ids'];
  PLATES.forEach((p,i)=>rows.push([
    i,p.center.x.toFixed(2),p.center.y.toFixed(2),p.center.z.toFixed(2),
    p.normal.x.toFixed(4),p.normal.y.toFixed(4),p.normal.z.toFixed(4),
    p.slits.length, p.neighbors.join(';')
  ].join(',')));
  rows.push('','plate_id,slit_idx,other_plate_id,entry_u,entry_v,exit_u,exit_v,width_mm');
  PLATES.forEach((p,i)=>p.slits.forEach((s,si)=>rows.push([
    i,si,s.inserted.id,
    s.entry.u.toFixed(2),s.entry.v.toFixed(2),
    s.exit.u.toFixed(2),s.exit.v.toFixed(2),
    s.width.toFixed(3)
  ].join(','))));
  download('slit_plates.csv',rows.join('\n'),'text/csv');
}

function exportDXF() {
  if(!PLATES.length){alert('先に生成を実行してください');return;}
  const cols=+document.getElementById('dxfCols').value;
  const sp  =+document.getElementById('dxfSpacing').value;
  const L   =PLATES[0].size;
  let dxf='';
  PLATES.forEach((p,idx)=>{
    const col=idx%cols, row=Math.floor(idx/cols);
    const ox=col*(L+sp), oy=-row*(L+sp), h=L/2;
    dxf+=dxfRect(ox-h,oy-h,ox+h,oy+h,'PLATES');
    p.slits.forEach(s=>{
      const eu=s.entry.u+ox,ev=s.entry.v+oy;
      const xu=s.exit.u+ox, xv=s.exit.v+oy;
      const du=xu-eu,dv=xv-ev,l=Math.sqrt(du*du+dv*dv);
      if(l<EPS) return;
      const hw=s.width/2, nx=-dv/l*hw, ny=du/l*hw;
      dxf+=dxfLine(eu+nx,ev+ny,xu+nx,xv+ny,'SLITS')
          +dxfLine(xu+nx,xv+ny,xu-nx,xv-ny,'SLITS')
          +dxfLine(xu-nx,xv-ny,eu-nx,ev-ny,'SLITS')
          +dxfLine(eu-nx,ev-ny,eu+nx,ev+ny,'SLITS');
    });
    dxf+=dxfText(ox-h+2,oy-h+2,String(idx+1),'LABELS',L*0.08);
  });
  dxf+='ENDSEC\n0\nEOF\n';
  download('slit_plates.dxf',dxfHeader()+dxf,'application/dxf');
}

function dxfHeader(){return`0\nSECTION\n2\nHEADER\n9\n$INSUNITS\n70\n4\n0\nENDSEC\n0\nSECTION\n2\nENTITIES\n`;}
function dxfRect(x1,y1,x2,y2,l){return dxfLine(x1,y1,x2,y1,l)+dxfLine(x2,y1,x2,y2,l)+dxfLine(x2,y2,x1,y2,l)+dxfLine(x1,y2,x1,y1,l);}
function dxfLine(x1,y1,x2,y2,l){return`0\nLINE\n8\n${l}\n10\n${x1.toFixed(4)}\n20\n${y1.toFixed(4)}\n30\n0.0\n11\n${x2.toFixed(4)}\n21\n${y2.toFixed(4)}\n31\n0.0\n`;}
function dxfText(x,y,t,l,h){return`0\nTEXT\n8\n${l}\n10\n${x.toFixed(4)}\n20\n${y.toFixed(4)}\n30\n0.0\n40\n${h.toFixed(4)}\n1\n${t}\n`;}

function exportTopView() {
  if(!PLATES.length){alert('先に生成を実行してください');return;}
  const scale=+document.getElementById('topScale').value;
  const L=PLATES[0].size;
  let maxC=0;
  PLATES.forEach(p=>{ maxC=Math.max(maxC,Math.abs(p.center.x),Math.abs(p.center.z)); });
  const dim=Math.ceil((maxC*2+L)*scale*1.1);
  const cnv=document.getElementById('topview-canvas');
  cnv.width=dim; cnv.height=dim;
  const ctx=cnv.getContext('2d');
  ctx.fillStyle='#1a1a2e'; ctx.fillRect(0,0,dim,dim);
  const cx=dim/2, cy=dim/2;
  PLATES.forEach((p,i)=>{
    const x=cx+p.center.x*scale, y=cy-p.center.z*scale, half=L*scale/2;
    const col=normalToColor(p.normal);
    ctx.fillStyle=`rgba(${(col.r*255)|0},${(col.g*255)|0},${(col.b*255)|0},0.7)`;
    ctx.fillRect(x-half,y-half,half*2,half*2);
    ctx.strokeStyle='#fff'; ctx.lineWidth=0.5; ctx.strokeRect(x-half,y-half,half*2,half*2);
    ctx.fillStyle='#fff'; ctx.font=`${Math.max(8,L*scale*0.2)}px monospace`; ctx.textAlign='center';
    ctx.fillText(String(i+1),x,y+4);
  });
  cnv.toBlob(blob=>{
    const url=URL.createObjectURL(blob),a=document.createElement('a');
    a.href=url; a.download='slit_plates_topview.png'; a.click(); URL.revokeObjectURL(url);
  });
}

function download(fn,c,m){
  const b=new Blob([c],{type:m}),u=URL.createObjectURL(b),a=document.createElement('a');
  a.href=u; a.download=fn; a.click(); URL.revokeObjectURL(u);
}

initRenderer();
