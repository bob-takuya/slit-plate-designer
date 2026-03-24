// ============================================================
// v8 algorithm test — Node.js
// ============================================================

class V3 {
  constructor(x=0,y=0,z=0) { this.x=x; this.y=y; this.z=z; }
  clone() { return new V3(this.x,this.y,this.z); }
}

function dot(a,b) { return a.x*b.x+a.y*b.y+a.z*b.z; }
function cross(a,b) { return new V3(a.y*b.z-a.z*b.y, a.z*b.x-a.x*b.z, a.x*b.y-a.y*b.x); }
function sub(a,b)   { return new V3(a.x-b.x,a.y-b.y,a.z-b.z); }
function add(a,b)   { return new V3(a.x+b.x,a.y+b.y,a.z+b.z); }
function scale(v,s) { return new V3(v.x*s,v.y*s,v.z*s); }
function normalize(v) { const l=Math.sqrt(dot(v,v)); return l<1e-12?new V3(0,0,1):scale(v,1/l); }
function vlen(v) { return Math.sqrt(dot(v,v)); }
function dist(a,b) { return vlen(sub(a,b)); }

// ---- Seeded RNG ----
function makeRng(seed) {
  let s = ((seed|0) >>> 0) + 1;
  return () => { s = Math.imul(1664525,s)+1013904223|0; return (s>>>0)/4294967296; };
}

// ---- Plate ----
class Plate {
  constructor(id, center, normal, size, thick) {
    this.id = id;
    this.center = center.clone();
    this.normal = normalize(normal);
    this.size = size; this.thick = thick;
    this.slits = []; this.neighbors = [];
    this._buildFrame();
  }
  _buildFrame() {
    const n = this.normal;
    const h = Math.abs(n.y)<0.9 ? new V3(0,1,0) : new V3(1,0,0);
    this.u = normalize(cross(n,h));
    this.v = normalize(cross(n,this.u));
  }
  localToWorld(pu,pv,pn=0) {
    return add(add(add(scale(this.u,pu),scale(this.v,pv)),scale(this.normal,pn)),this.center);
  }
  worldToLocal(pt) {
    const d=sub(pt,this.center);
    return {u:dot(d,this.u),v:dot(d,this.v),n:dot(d,this.normal)};
  }
  inBounds(pu,pv,margin=0) { const h=this.size/2-margin; return Math.abs(pu)<=h&&Math.abs(pv)<=h; }
  obb() { return {center:this.center,axes:[this.u,this.v,this.normal],halfExtents:[this.size/2,this.size/2,this.thick/2]}; }
  obbCorners() {
    const corners=[]; const h=this.size/2,ht=this.thick/2;
    for(const su of[-1,1]) for(const sv of[-1,1]) for(const sn of[-1,1])
      corners.push(this.localToWorld(su*h,sv*h,sn*ht));
    return corners;
  }
}

// ---- OBB-OBB SAT ----
function obbIntersect(A,B) {
  const D=sub(B.center,A.center);
  const axes=[...A.axes,...B.axes];
  for(const a of A.axes) for(const b of B.axes) { const c=cross(a,b); if(dot(c,c)>1e-10) axes.push(normalize(c)); }
  for(const ax of axes) {
    let pA=0; for(let i=0;i<3;i++) pA+=A.halfExtents[i]*Math.abs(dot(A.axes[i],ax));
    let pB=0; for(let i=0;i<3;i++) pB+=B.halfExtents[i]*Math.abs(dot(B.axes[i],ax));
    if(Math.abs(dot(D,ax))>pA+pB+1e-6) return false;
  }
  return true;
}

// ---- Plane-plane intersection line ----
function planeIntersectionLine(pA,pB) {
  const lineDir=normalize(cross(pA.normal,pB.normal));
  if(dot(lineDir,lineDir)<0.01) return null;
  const dA=dot(pA.normal,pA.center), dB=dot(pB.normal,pB.center);
  const n1n2=dot(pA.normal,pB.normal), det=1-n1n2*n1n2;
  if(Math.abs(det)<1e-8) return null;
  const c1=(dA-n1n2*dB)/det, c2=(dB-n1n2*dA)/det;
  const linePoint=add(scale(pA.normal,c1),scale(pB.normal,c2));
  return {linePoint,lineDir};
}

// ---- KEY FIX: Parametric slab clipping ----
function clipLineToPlate(plate, linePoint, lineDir) {
  const lp=sub(linePoint,plate.center);
  const pu0=dot(lp,plate.u), du=dot(lineDir,plate.u);
  const pv0=dot(lp,plate.v), dv=dot(lineDir,plate.v);
  const h=plate.size/2;
  let tMin=-1e9, tMax=1e9;

  if(Math.abs(du)<1e-9) {
    if(Math.abs(pu0)>h+1e-4) return null;
  } else {
    const t1=(-h-pu0)/du, t2=(h-pu0)/du;
    tMin=Math.max(tMin,Math.min(t1,t2)); tMax=Math.min(tMax,Math.max(t1,t2));
  }
  if(Math.abs(dv)<1e-9) {
    if(Math.abs(pv0)>h+1e-4) return null;
  } else {
    const t1=(-h-pv0)/dv, t2=(h-pv0)/dv;
    tMin=Math.max(tMin,Math.min(t1,t2)); tMax=Math.min(tMax,Math.max(t1,t2));
  }
  if(tMax-tMin<1e-6) return null;
  return [tMin,tMax];
}

// ---- Slit building on one plate ----
function snapToEdge(pt, other, half) {
  const du=other.u-pt.u, dv=other.v-pt.v;
  const len=Math.sqrt(du*du+dv*dv);
  if(len<1e-9) return {u:Math.sign(pt.u||1)*half,v:pt.v};
  let t=Infinity;
  if(Math.abs(du)>1e-9) {
    const t1=(half-pt.u)/du; if(t1>1e-6) t=Math.min(t,t1);
    const t2=(-half-pt.u)/du; if(t2>1e-6) t=Math.min(t,t2);
  }
  if(Math.abs(dv)>1e-9) {
    const t1=(half-pt.v)/dv; if(t1>1e-6) t=Math.min(t,t1);
    const t2=(-half-pt.v)/dv; if(t2>1e-6) t=Math.min(t,t2);
  }
  if(!isFinite(t)) return pt;
  return {u:pt.u+du*t,v:pt.v+dv*t};
}

function buildSlitOnPlate(host, inserted, linePoint, lineDir, tMin, tMax, tol) {
  const half=host.size/2;
  const wEnd=add(linePoint,scale(lineDir,tMin));
  const wOther=add(linePoint,scale(lineDir,tMax));
  const lEnd=host.worldToLocal(wEnd);
  const lOther=host.worldToLocal(wOther);
  const clamp=p=>({u:Math.max(-half,Math.min(half,p.u)),v:Math.max(-half,Math.min(half,p.v))});
  const cEnd=clamp(lEnd), cOther=clamp(lOther);
  const distToEdge=p=>half-Math.max(Math.abs(p.u),Math.abs(p.v));
  const du=cOther.u-cEnd.u, dv=cOther.v-cEnd.v;
  if(Math.sqrt(du*du+dv*dv)<inserted.thick*2) return null;
  let entry,exit;
  if(distToEdge(cEnd)<distToEdge(cOther)) {
    entry=snapToEdge(cEnd,cOther,half); exit=cOther;
  } else {
    entry=snapToEdge(cOther,cEnd,half); exit=cEnd;
  }
  if(!host.inBounds(exit.u,exit.v,host.thick*0.5)) return null;
  if(distToEdge(entry)>host.size*0.03) return null;
  return {host,inserted,entry,exit,width:inserted.thick*tol};
}

// ---- Compute slits between two perpendicular plates (FIXED) ----
function computeSlits(pA, pB, tol=1.2) {
  // Must be roughly perpendicular
  if(Math.abs(dot(pA.normal,pB.normal))>0.3) return null;
  const line=planeIntersectionLine(pA,pB);
  if(!line) return null;
  const {linePoint,lineDir}=line;
  const rA=clipLineToPlate(pA,linePoint,lineDir);
  const rB=clipLineToPlate(pB,linePoint,lineDir);
  if(!rA||!rB) return null;
  const tMin=Math.max(rA[0],rB[0]), tMax=Math.min(rA[1],rB[1]);
  if(tMax-tMin<pA.thick*1.5) return null;
  const slitA=buildSlitOnPlate(pA,pB,linePoint,lineDir,tMin,tMax,tol);
  const slitB=buildSlitOnPlate(pB,pA,linePoint,lineDir,tMin,tMax,tol);
  if(!slitA||!slitB) return null;
  return {slitA,slitB};
}

// ---- Slit-slit overlap (2D AABB) ----
function slitsOverlap(s1,s2) {
  const expand=Math.max(s1.width,s2.width)/2+1e-3;
  const aabb=s=>({
    minU:Math.min(s.entry.u,s.exit.u)-expand, maxU:Math.max(s.entry.u,s.exit.u)+expand,
    minV:Math.min(s.entry.v,s.exit.v)-expand, maxV:Math.max(s.entry.v,s.exit.v)+expand,
  });
  const a=aabb(s1),b=aabb(s2);
  return !(a.maxU<b.minU||b.maxU<a.minU||a.maxV<b.minV||b.maxV<a.minV);
}

// ============================================================
// v8 Greedy Growth Optimizer
// ============================================================
function runOptimize({ size=100, thick=3, radius=300, slitTol=1.2, seed=42, maxPlates=200 }={}) {
  const rng=makeRng(seed);

  // Seed plate: random position on sphere, random tangential normal
  function randomOnSphere() {
    const phi=Math.acos(1-2*rng()), theta=2*Math.PI*rng();
    return new V3(radius*Math.sin(phi)*Math.cos(theta), radius*Math.cos(phi), radius*Math.sin(phi)*Math.sin(theta));
  }
  function randomTangent(pos) {
    const r=normalize(pos);
    const h=Math.abs(r.y)<0.9?new V3(0,1,0):new V3(1,0,0);
    const t1=normalize(cross(r,h)), t2=normalize(cross(r,t1));
    const a=rng()*2*Math.PI;
    return normalize(add(scale(t1,Math.cos(a)),scale(t2,Math.sin(a))));
  }

  const c0=randomOnSphere();
  const plates=[new Plate(0,c0,randomTangent(c0),size,thick)];
  console.log(`Seed: (${c0.x.toFixed(0)},${c0.y.toFixed(0)},${c0.z.toFixed(0)})`);

  // Growth parameters
  const N_THETA=16;
  const STEP_MULTS=[0.4,0.55,0.7,0.85,1.0,1.15,-0.4,-0.55,-0.7,-0.85,-1.0,-1.15];

  let stepsWithoutImprovement=0;
  const MAX_STALE=3;

  while(plates.length<maxPlates) {
    let best=null, bestScore=-Infinity;

    for(const pA of plates) {
      for(let ti=0;ti<N_THETA;ti++) {
        const theta=(ti/N_THETA)*2*Math.PI;
        // New plate's normal: perpendicular to pA.normal, in pA's plane
        const n_B=normalize(add(scale(pA.u,Math.cos(theta)),scale(pA.v,Math.sin(theta))));
        // Intersection line direction (always perpendicular to both normals)
        const lineDir=normalize(cross(pA.normal,n_B));

        for(const sm of STEP_MULTS) {
          const step=sm*size;
          const c_B_raw=add(pA.center,scale(lineDir,step));
          const c_B=scale(normalize(c_B_raw),radius); // project to sphere

          // Skip if nearly same position as pA (radial direction case)
          const d_pA=dist(c_B,pA.center);
          if(d_pA<size*0.25) continue;

          // PDS criterion: min distance to ALL existing plates
          let minDist=Infinity;
          for(const p of plates) {
            const d=dist(c_B,p.center);
            if(d<minDist) minDist=d;
          }
          // Require minimum spacing
          if(minDist<size*0.25) continue;

          const pB=new Plate(plates.length,c_B,n_B,size,thick);

          // Check slit with parent
          const result=computeSlits(pA,pB,slitTol);
          if(!result) continue;

          // Check slit overlap on pA
          let slitOverlap=false;
          for(const s of pA.slits) { if(slitsOverlap(s,result.slitA)){slitOverlap=true;break;} }
          if(slitOverlap) continue;

          // Check physical interference with all plates EXCEPT pA
          let interferes=false;
          for(const p of plates) {
            if(p===pA) continue;
            if(obbIntersect(p.obb(),pB.obb())){interferes=true;break;}
          }
          if(interferes) continue;

          // Score: maximize min-distance (PDS = uniform coverage)
          if(minDist>bestScore) {
            bestScore=minDist;
            best={pA,pB,result};
          }
        }
      }
    }

    if(!best) break;

    // Commit best candidate
    const {pA,pB,result}=best;
    pA.slits.push(result.slitA);
    pB.slits.push(result.slitB);
    pA.neighbors.push(pB.id);
    pB.neighbors.push(pA.id);
    plates.push(pB);

    console.log(`[${plates.length}] c=(${pB.center.x.toFixed(1)},${pB.center.y.toFixed(1)},${pB.center.z.toFixed(1)}) score=${bestScore.toFixed(1)}`);
  }

  // Verify connectivity (should always be true for tree growth)
  const visited=new Set([0]);
  const q=[0];
  while(q.length){const id=q.shift();for(const nb of plates[id].neighbors){if(!visited.has(nb)){visited.add(nb);q.push(nb);}}}
  const connected=visited.size===plates.length;

  console.log(`\n=== RESULT ===`);
  console.log(`Plates: ${plates.length}`);
  console.log(`Connected: ${connected ? '✓' : '✗ FAIL'}`);

  // Sphere deviation
  let avgDev=0,maxDev=0;
  for(const p of plates) {
    const d=Math.abs(vlen(p.center)-radius);
    avgDev+=d; maxDev=Math.max(maxDev,d);
  }
  avgDev/=plates.length;
  console.log(`Sphere deviation: avg=${avgDev.toFixed(2)}mm max=${maxDev.toFixed(2)}mm (R=${radius})`);
  console.log(`Slits per plate: avg=${(plates.reduce((a,p)=>a+p.slits.length,0)/plates.length).toFixed(2)}`);

  return plates;
}

// Run tests
console.log('=== TEST seed=42, R=300, L=100 ===');
runOptimize({size:100,thick:3,radius:300,seed:42,maxPlates:150});

console.log('\n=== TEST seed=123, R=300, L=100 ===');
runOptimize({size:100,thick:3,radius:300,seed:123,maxPlates:150});

console.log('\n=== TEST seed=7, R=200, L=80 ===');
runOptimize({size:80,thick:3,radius:200,seed:7,maxPlates:100});
