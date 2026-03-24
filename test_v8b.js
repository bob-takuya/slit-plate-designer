// === v8b: Random sampling + step optimization ===
// Copy core functions from test_v8.js
const fs = require('fs');
const src = fs.readFileSync('/tmp/slit-plate-designer/test_v8.js','utf8');
// Grab everything up to the runOptimize function
eval(src.split('// ============================================================\n// v8 Greedy Growth Optimizer')[0]);

function runOptimizeV8b({ size=100, thick=3, radius=300, slitTol=1.2, seed=42, maxPlates=200, nRandom=80 }={}) {
  const rng = makeRng(seed);

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

  // Fine step grid for line search
  const STEPS = [];
  for(let i=-1.2; i<=1.21; i+=0.15) if(Math.abs(i)>0.15) STEPS.push(i);

  let stuckCount = 0;

  while(plates.length < maxPlates) {
    const candidates = [];

    // ランダムN回試行: (pA=random, θ=random) → step最適化
    for(let trial=0; trial<nRandom; trial++) {
      // ランダムに親プレートを選ぶ
      const pA = plates[Math.floor(rng() * plates.length)];
      // ランダムな角度
      const theta = rng() * 2 * Math.PI;
      const n_B = normalize(add(scale(pA.u,Math.cos(theta)), scale(pA.v,Math.sin(theta))));
      const lineDir = normalize(cross(pA.normal, n_B));

      // step最適化: 球面上で拘束を満たしつつmin距離最大
      let bestScore = -Infinity, bestStep = null;

      for(const sm of STEPS) {
        const c_B_raw = add(pA.center, scale(lineDir, sm*size));
        const c_B = scale(normalize(c_B_raw), radius);

        if(dist(c_B,pA.center) < size*0.2) continue;

        // 最近傍距離（PDS基準）
        let minD = Infinity;
        for(const p of plates) { const d=dist(c_B,p.center); if(d<minD) minD=d; }
        if(minD < size*0.2) continue;

        const pB = new Plate(plates.length, c_B, n_B, size, thick);

        // 拘束1: スリット成立
        const result = computeSlits(pA, pB, slitTol);
        if(!result) continue;

        // 拘束2: pAの既存スリットと重複なし
        let slitOK = true;
        for(const s of pA.slits) { if(slitsOverlap(s,result.slitA)){slitOK=false;break;} }
        if(!slitOK) continue;

        // 拘束3: 物理干渉なし（pA以外）
        let noInter = true;
        for(const p of plates) {
          if(p===pA) continue;
          if(obbIntersect(p.obb(),pB.obb())){noInter=false;break;}
        }
        if(!noInter) continue;

        if(minD > bestScore) {
          bestScore = minD;
          bestStep = { c_B, n_B, result, pA, score: minD };
        }
      }

      if(bestStep) candidates.push(bestStep);
    }

    if(candidates.length === 0) {
      stuckCount++;
      if(stuckCount >= 3) break;  // 3回連続でゼロなら終了
      continue;
    }
    stuckCount = 0;

    // 候補の中から最良を選ぶ（min距離最大 = 最も孤立した位置）
    candidates.sort((a,b) => b.score - a.score);
    const best = candidates[0];

    const { pA, c_B, n_B, result } = best;
    const pB = new Plate(plates.length, c_B, n_B, size, thick);
    pA.slits.push(result.slitA);
    pB.slits.push(result.slitB);
    pA.neighbors.push(pB.id);
    pB.neighbors.push(pA.id);
    plates.push(pB);

    if(plates.length % 10 === 0)
      console.log(`[${plates.length}] score=${best.score.toFixed(1)}, candidates=${candidates.length}`);
  }

  // 連結性確認
  const vis=new Set([0]), q=[0];
  while(q.length){const id=q.shift();for(const nb of plates[id].neighbors){if(!vis.has(nb)){vis.add(nb);q.push(nb);}}}
  console.log(`Plates: ${plates.length}, Connected: ${vis.size===plates.length?'✓':'✗'}, DevSphere: 0mm`);
  return plates;
}

console.log('=== v8b seed=42 ===');
runOptimizeV8b({seed:42, maxPlates:150});
console.log('\n=== v8b seed=123 (was stuck at 8) ===');
runOptimizeV8b({seed:123, maxPlates:150});
console.log('\n=== v8b seed=999 ===');
runOptimizeV8b({seed:999, maxPlates:150});
