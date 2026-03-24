// Node.js test for v7 equal-area sampling algorithm
// 
// Problem: current UV grid has polar bias because φ is sampled uniformly in [0, π]
// Fix: sample φ such that cos(φ) is uniform → equal-area distribution
//
// Additional: optimal plate count formula

function fibTest() {
  const R = 300, L = 100;
  const densityHint = 40;

  // OLD formula
  const oldNU = Math.max(3, Math.round(Math.sqrt(densityHint * 1.6)));
  const oldNV = Math.max(3, Math.round(densityHint * 1.6 / oldNU));
  console.log(`OLD: nU=${oldNU}, nV=${oldNV}, total=${oldNU*oldNV}`);

  // OLD sampling - uniform φ
  let oldBias = 0;
  for (let ui = 0; ui < oldNU; ui++) {
    for (let vi = 0; vi < oldNV; vi++) {
      const tNorm = (vi + 0.5) / oldNV;
      const phi = tNorm * Math.PI * 0.8 + 0.1 * Math.PI;
      // Near pole: phi < 0.3 or phi > 2.84 (< 17° or > 163°)
      if (phi < 0.3 || phi > Math.PI - 0.3) oldBias++;
    }
  }
  console.log(`OLD: polar cells (< 17° or > 163°): ${oldBias} / ${oldNU*oldNV} = ${(100*oldBias/(oldNU*oldNV)).toFixed(1)}%`);

  // NEW formula - 2:1 ratio
  const newNV = Math.max(3, Math.round(Math.sqrt(densityHint * 0.8)));
  const newNU = Math.max(4, Math.round(newNV * 2));
  console.log(`NEW: nU=${newNU}, nV=${newNV}, total=${newNU*newNV}`);

  // NEW sampling - equal-area (uniform in cos φ)
  let newBias = 0;
  let latDistribution = new Array(9).fill(0);
  for (let ui = 0; ui < newNU; ui++) {
    for (let vi = 0; vi < newNV; vi++) {
      const tNorm = (vi + 0.5) / newNV;
      const phi = Math.acos(1 - 2 * tNorm);
      if (phi < 0.3 || phi > Math.PI - 0.3) newBias++;
      // Track latitude distribution (0°-90° in 9 bands)
      const latBand = Math.min(8, Math.floor(phi / Math.PI * 9));
      latDistribution[latBand]++;
    }
  }
  console.log(`NEW: polar cells (< 17° or > 163°): ${newBias} / ${newNU*newNV} = ${(100*newBias/(newNU*newNV)).toFixed(1)}%`);
  console.log(`NEW: latitude distribution (0°→180° in 9 bands):`, latDistribution.join(', '));

  // Optimal plate count
  const N_optimal = Math.round(4 * Math.PI * R * R / (L * L));
  console.log(`\nOptimal plate count for R=${R}, L=${L}: ~${N_optimal} plates`);
  console.log(`  → densityHint to achieve this: ${Math.round(N_optimal * 1.4)}`);

  // Test equal area property: each φ-band should have equal count
  console.log(`\nEqual area check: each band should have ${newNU*newNV/9} cells`);
  const variance = latDistribution.reduce((acc, v) => acc + Math.pow(v - newNU*newNV/9, 2), 0) / 9;
  console.log(`Variance: ${variance.toFixed(2)} (lower = more uniform)`);
}

fibTest();
