// ============================================================
// Slit Plate Designer v2 — Revised Engine
// 
// Key changes from v1:
//  - Normals are free (sphere surface tangent planes, not XYZ-aligned)
//  - OBB-OBB strict interference via Separating Axis Theorem (SAT)
//  - Automatic density: greedy plate addition under hard constraints
//    (zero-interference + single connected component)
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
function cross(a, b) { return new V3(a.y*b.z - a.z*b.y, a.z*b.x - a.x*b.z, a.x*b.y - a.y*b.x); }
function sub(a, b) { return new V3(a.x-b.x, a.y-b.y, a.z-b.z); }
function add(a, b) { return new V3(a.x+b.x, a.y+b.y, a.z+b.z); }
function scale(v, s) { return new V3(v.x*s, v.y*s, v.z*s); }
function normalize(v) { const l = Math.sqrt(dot(v,v)); return l<1e-12?new V3(0,0,1):scale(v,1/l); }

// Fibonacci sphere
function fibonacciSphere(n) {
  const pts = [];
  const phi = Math.PI * (3 - Math.sqrt(5));
  for (let i = 0; i < n; i++) {
    const y = 1 - (i / (n - 1)) * 2;
    const r = Math.sqrt(Math.max(0, 1 - y*y));
    const theta = phi * i;
    pts.push(new V3(r*Math.cos(theta), y, r*Math.sin(theta)));
  }
  return pts;
}

// ============================================================
// Plate class
// Each plate is a square of side `size` and depth `thickness`.
// Normal = outward direction (perpendicular to plate surface).
// ============================================================
class Plate {
  constructor(id, center, normal, size, thickness) {
    this.id = id;
    this.center = center.clone();
    this.normal = normalize(normal);
    this.size = size;
    this.thick = thickness;
    this.slits = [];      // Slit[]
    this.neighbors = [];  // connected plate ids

    // Build orthonormal frame: (u, v, normal)
    this._buildFrame();
  }

  _buildFrame() {
    const n = this.normal;
    // Pick an arbitrary vector not parallel to n
    const helper = Math.abs(n.y) < 0.9 ? new V3(0,1,0) : new V3(1,0,0);
    this.u = normalize(cross(n, helper));
    this.v = normalize(cross(n, this.u));
  }

  // World ← local(pu, pv, pn)
  localToWorld(pu, pv, pn=0) {
    return add(add(add(scale(this.u, pu), scale(this.v, pv)), scale(this.normal, pn)), this.center);
  }

  // Inverse: project world point onto plate's local coords
  worldToLocal(pt) {
    const d = sub(pt, this.center);
    return { u: dot(d, this.u), v: dot(d, this.v), n: dot(d, this.normal) };
  }

  // Is (pu, pv) inside plate boundary?
  inBounds(pu, pv, margin=0) {
    const h = this.size/2 - margin;
    return Math.abs(pu) <= h && Math.abs(pv) <= h;
  }

  // 8 corners of the OBB in world coords
  obbCorners() {
    const h = this.size/2, ht = this.thick/2;
    const corners = [];
    for (const su of [-1, 1]) for (const sv of [-1, 1]) for (const sn of [-1, 1])
      corners.push(this.localToWorld(su*h, sv*h, sn*ht));
    return corners;
  }

  // OBB description: {center, axes:[u,v,n], halfExtents:[h,h,ht]}
  obb() {
    return {
      center: this.center,
      axes: [this.u, this.v, this.normal],
      halfExtents: [this.size/2, this.size/2, this.thick/2]
    };
  }
}

// ============================================================
// OBB-OBB Intersection Test (Separating Axis Theorem)
// Returns true if the two OBBs INTERSECT (overlap).
// ============================================================
function obbIntersect(obbA, obbB) {
  const D = sub(obbB.center, obbA.center);
  const axes = [];

  // 3 face normals of A
  for (const ax of obbA.axes) axes.push(ax);
  // 3 face normals of B
  for (const bx of obbB.axes) axes.push(bx);
  // 9 cross products
  for (const ax of obbA.axes)
    for (const bx of obbB.axes) {
      const c = cross(ax, bx);
      if (dot(c,c) > 1e-10) axes.push(normalize(c));
    }

  for (const axis of axes) {
    // Project A
    let pA = 0;
    for (let i=0; i<3; i++) pA += obbA.halfExtents[i] * Math.abs(dot(obbA.axes[i], axis));
    // Project B
    let pB = 0;
    for (let i=0; i<3; i++) pB += obbB.halfExtents[i] * Math.abs(dot(obbB.axes[i], axis));
    // Distance along axis
    const dist = Math.abs(dot(D, axis));
    if (dist > pA + pB + 1e-6) return false; // separating axis found
  }
  return true; // no separating axis → intersecting
}

// ============================================================
// Compute intersection line of two planes defined by plates.
// Returns { linePoint, lineDir } or null if parallel.
// ============================================================
function planeIntersectionLine(pA, pB) {
  const lineDir = normalize(cross(pA.normal, pB.normal));
  if (dot(lineDir, lineDir) < 0.01) return null; // nearly parallel

  // Find a point on the line: solve system of two plane equations
  const dA = dot(pA.normal, pA.center);
  const dB = dot(pB.normal, pB.center);
  const n1n2 = dot(pA.normal, pB.normal);
  const det = 1 - n1n2*n1n2;
  if (Math.abs(det) < 1e-8) return null;
  const c1 = (dA - n1n2*dB)/det;
  const c2 = (dB - n1n2*dA)/det;
  const linePoint = add(scale(pA.normal, c1), scale(pB.normal, c2));
  return { linePoint, lineDir };
}

// Project plate boundary onto line, return [tMin, tMax] or null
function projectPlateOnLine(plate, linePoint, lineDir) {
  const h = plate.size/2;
  const ht = plate.thick/2;
  const corners = plate.obbCorners();
  const ts = corners.map(c => dot(sub(c, linePoint), lineDir));
  const tMin = Math.min(...ts), tMax = Math.max(...ts);
  // Check that midpoint of segment is within plate's 2D boundary
  const tMid = (tMin+tMax)/2;
  const midPt = add(linePoint, scale(lineDir, tMid));
  const loc = plate.worldToLocal(midPt);
  if (!plate.inBounds(loc.u, loc.v, plate.size*0.05)) return null;
  return [tMin, tMax];
}

// Snap a local point toward the plate edge along direction toward `other`
function snapToEdge(pt, other, half) {
  const du = other.u - pt.u, dv = other.v - pt.v;
  const len = Math.sqrt(du*du + dv*dv);
  if (len < 1e-9) return { u: Math.sign(pt.u||1)*half, v: pt.v };
  let t = Infinity;
  if (Math.abs(du) > 1e-9) {
    const t1 = (half - pt.u)/du;  if (t1 > 1e-6) t = Math.min(t, t1);
    const t2 = (-half - pt.u)/du; if (t2 > 1e-6) t = Math.min(t, t2);
  }
  if (Math.abs(dv) > 1e-9) {
    const t1 = (half - pt.v)/dv;  if (t1 > 1e-6) t = Math.min(t, t1);
    const t2 = (-half - pt.v)/dv; if (t2 > 1e-6) t = Math.min(t, t2);
  }
  if (!isFinite(t)) return pt;
  return { u: pt.u+du*t, v: pt.v+dv*t };
}

// ============================================================
// Compute slit geometry for a perpendicular pair.
// Returns { slitA, slitB } or null if invalid.
// ============================================================
function computeSlits(pA, pB, tol) {
  const line = planeIntersectionLine(pA, pB);
  if (!line) return null;
  const { linePoint, lineDir } = line;

  const rA = projectPlateOnLine(pA, linePoint, lineDir);
  const rB = projectPlateOnLine(pB, linePoint, lineDir);
  if (!rA || !rB) return null;

  const tMin = Math.max(rA[0], rB[0]);
  const tMax = Math.min(rA[1], rB[1]);
  if (tMax - tMin < pA.thick * 1.5) return null; // too short

  const slitA = buildSlitOnPlate(pA, pB, linePoint, lineDir, tMin, tMax, tol);
  const slitB = buildSlitOnPlate(pB, pA, linePoint, lineDir, tMin, tMax, tol);
  if (!slitA || !slitB) return null;
  return { slitA, slitB };
}

function buildSlitOnPlate(host, inserted, linePoint, lineDir, tMin, tMax, tol) {
  const half = host.size/2;
  const wEnd = add(linePoint, scale(lineDir, tMin));
  const wOther = add(linePoint, scale(lineDir, tMax));
  const lEnd = host.worldToLocal(wEnd);
  const lOther = host.worldToLocal(wOther);

  const clamp = p => ({ u: Math.max(-half, Math.min(half, p.u)), v: Math.max(-half, Math.min(half, p.v)) });
  const cEnd = clamp(lEnd), cOther = clamp(lOther);

  const du = cOther.u - cEnd.u, dv = cOther.v - cEnd.v;
  const len = Math.sqrt(du*du + dv*dv);
  if (len < inserted.thick * 2) return null;

  const distToEdge = p => half - Math.max(Math.abs(p.u), Math.abs(p.v));
  let entry, exit;
  if (distToEdge(cEnd) < distToEdge(cOther)) {
    entry = snapToEdge(cEnd, cOther, half);
    exit = cOther;
  } else {
    entry = snapToEdge(cOther, cEnd, half);
    exit = cEnd;
  }

  // Validate: exit must be strictly inside
  if (!host.inBounds(exit.u, exit.v, host.thick * 0.5)) return null;
  // Entry must be on edge (within tolerance)
  if (distToEdge(entry) > host.size * 0.02) return null;

  return { host, inserted, entry, exit, width: inserted.thick * tol };
}

// Check two slits on same plate for overlap (2D AABB)
function slitsOverlap(s1, s2) {
  const expand = Math.max(s1.width, s2.width) / 2 + 1e-3;
  function aabb(s) {
    return {
      minU: Math.min(s.entry.u, s.exit.u) - expand,
      maxU: Math.max(s.entry.u, s.exit.u) + expand,
      minV: Math.min(s.entry.v, s.exit.v) - expand,
      maxV: Math.max(s.entry.v, s.exit.v) + expand,
    };
  }
  const a = aabb(s1), b = aabb(s2);
  return !(a.maxU < b.minU || b.maxU < a.minU || a.maxV < b.minV || b.maxV < a.minV);
}

// ============================================================
// Check if two plates physically interfere.
// Connected plates (sharing a slit) are allowed to intersect
// along their slit only. Here we use a conservative check:
// If their OBBs DON'T intersect → no interference.
// If OBBs DO intersect AND they are NOT connected → interference.
// (Connected plates are handled by their slit geometry.)
// ============================================================
function platesInterfere(pA, pB) {
  return obbIntersect(pA.obb(), pB.obb());
}

// ============================================================
// BFS connectivity
// ============================================================
function largestComponent(plates) {
  if (!plates.length) return [];
  const adj = new Map(plates.map(p => [p.id, new Set(p.neighbors)]));
  const visited = new Set();
  let best = [];
  for (const p of plates) {
    if (visited.has(p.id)) continue;
    const comp = [];
    const q = [p.id];
    while (q.length) {
      const id = q.shift();
      if (visited.has(id)) continue;
      visited.add(id); comp.push(id);
      (adj.get(id) || new Set()).forEach(nid => { if (!visited.has(nid)) q.push(nid); });
    }
    if (comp.length > best.length) best = comp;
  }
  return best;
}

// ============================================================
// Main Optimizer
// ============================================================
let PLATES = [];

async function runOptimize() {
  const size = +document.getElementById('plateSize').value;
  const thick = +document.getElementById('plateThick').value;
  const radius = +document.getElementById('targetRadius').value;
  const shape = document.getElementById('targetShape').value;
  const densityHint = +document.getElementById('density').value;
  const slitTol = +document.getElementById('slitTol').value;
  const cylH = +document.getElementById('cylHeight').value;

  document.getElementById('log').textContent = '';
  LOG('Phase 1: Generating candidate plates...');

  // --- 1. Dense candidate set on target surface ---
  // Use 3× the requested density, then greedily prune
  const nCandidates = densityHint * 3;
  let rawPts;
  if (shape === 'sphere') {
    rawPts = fibonacciSphere(nCandidates).map(p => scale(p, radius));
  } else if (shape === 'hemisphere') {
    rawPts = fibonacciSphere(nCandidates * 2)
      .filter(p => p.y >= -0.05)
      .slice(0, nCandidates)
      .map(p => scale(normalize(p), radius));
  } else {
    // cylinder
    rawPts = [];
    for (let i = 0; i < nCandidates; i++) {
      const theta = (i / nCandidates) * Math.PI * 2;
      const y = (Math.random() - 0.5) * cylH;
      rawPts.push(new V3(radius * Math.cos(theta), y, radius * Math.sin(theta)));
    }
  }

  // --- 2. Build plates with FREE normals (tangent to surface) ---
  const candidates = rawPts.map((p, i) => {
    let normal;
    if (shape === 'cylinder') {
      // Normal points radially outward in XZ plane
      normal = normalize(new V3(p.x, 0, p.z));
    } else {
      // Normal = outward radial direction (sphere/hemisphere)
      normal = normalize(p);
    }
    return new Plate(i, p, normal, size, thick);
  });
  LOG(`${candidates.length} candidates generated`);

  // --- 3. Greedy plate selection under hard constraints ---
  // For each candidate (in random order), try to add it.
  // Hard constraints:
  //   C1: No physical interference with already-placed plates
  //       UNLESS a valid slit connection can be established.
  //   C2: Slit connections only when normals are ~perpendicular (|dot| < 0.15).
  //   C3: Slit geometry must be valid (entry on edge, exit interior, no slit overlap).
  //   C4: Final set must be a single connected component.
  //
  // We relax C4 to post-processing (keep largest component).

  // Shuffle to avoid systematic bias
  const shuffled = [...candidates].sort(() => Math.random() - 0.5);
  const placed = []; // Plate[]
  const placedMap = new Map(); // id → Plate

  LOG('Phase 2: Greedy placement (strict interference check)...');
  let skipped = 0;

  for (const cand of shuffled) {
    // Check against all placed plates
    let canPlace = true;
    const pendingSlitsA = []; // slits to add to cand
    const pendingSlitsB = []; // [{plate, slit}] to add to placed plates
    const pendingNeighbors = []; // pairs to connect

    for (const existing of placed) {
      const interfere = platesInterfere(cand, existing);
      if (!interfere) continue; // no overlap → fine

      // OBBs overlap. Check if we can resolve with a slit joint.
      const perp = Math.abs(dot(cand.normal, existing.normal)) < 0.15;
      if (!perp) {
        // Not perpendicular → can't make slit joint → skip this candidate
        canPlace = false; break;
      }

      // Try to compute slit
      const result = computeSlits(cand, existing, slitTol);
      if (!result) {
        // Geometry doesn't work out → can't resolve → skip
        canPlace = false; break;
      }
      const { slitA, slitB } = result;

      // Check slit overlap with existing slits on cand
      let overlap = false;
      for (const s of pendingSlitsA) { if (slitsOverlap(s, slitA)) { overlap = true; break; } }
      if (!overlap) for (const s of existing.slits) { if (slitsOverlap(s, slitB)) { overlap = true; break; } }
      if (overlap) { canPlace = false; break; }

      pendingSlitsA.push(slitA);
      pendingSlitsB.push({ plate: existing, slit: slitB });
      pendingNeighbors.push(existing);
    }

    if (!canPlace) { skipped++; continue; }

    // Commit: add cand with its resolved slits
    for (const s of pendingSlitsA) cand.slits.push(s);
    for (const { plate, slit } of pendingSlitsB) plate.slits.push(slit);
    for (const nb of pendingNeighbors) {
      cand.neighbors.push(nb.id);
      nb.neighbors.push(cand.id);
    }
    placed.push(cand);
    placedMap.set(cand.id, cand);
  }
  LOG(`Placed: ${placed.length}, skipped: ${skipped}`);

  // --- 4. Keep largest connected component ---
  const compIds = new Set(largestComponent(placed));
  const final = placed.filter(p => compIds.has(p.id));

  // Clean up slits and neighbors referencing removed plates
  for (const p of final) {
    p.slits = p.slits.filter(s => compIds.has(s.inserted.id));
    p.neighbors = p.neighbors.filter(id => compIds.has(id));
  }

  LOG(`Connected component: ${final.length} / ${placed.length}`);
  PLATES = final;

  // --- 5. Stats ---
  const totalSlits = final.reduce((a, p) => a + p.slits.length, 0);
  STAT('st-plates', final.length);
  STAT('st-slits', totalSlits);
  STAT('st-connected', final.length === placed.length ? '✓ All' : `${final.length}/${placed.length}`);
  STAT('st-coverage', ((final.length / densityHint) * 100).toFixed(0) + '%');

  LOG('Rendering...');
  renderScene(final);
  LOG('Done.');
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

  scene = new THREE.Scene();
  camera = new THREE.PerspectiveCamera(60, canvas.clientWidth / canvas.clientHeight, 1, 20000);
  camera.position.set(0, 200, 800);

  scene.add(new THREE.AmbientLight(0xffffff, 0.5));
  const dl = new THREE.DirectionalLight(0xffffff, 0.9);
  dl.position.set(1, 2, 1); scene.add(dl);

  // Orbit controls
  let dragging = false, rightDrag = false;
  let lx = 0, ly = 0;
  let sph = { theta: 0.3, phi: 1.0, r: 800 };
  const target = new THREE.Vector3();

  function updateCam() {
    camera.position.set(
      target.x + sph.r * Math.sin(sph.phi) * Math.sin(sph.theta),
      target.y + sph.r * Math.cos(sph.phi),
      target.z + sph.r * Math.sin(sph.phi) * Math.cos(sph.theta)
    );
    camera.lookAt(target);
  }
  updateCam();

  const el = canvas;
  el.addEventListener('mousedown', e => { dragging=true; rightDrag=(e.button===2); lx=e.clientX; ly=e.clientY; e.preventDefault(); });
  el.addEventListener('contextmenu', e => e.preventDefault());
  window.addEventListener('mouseup', () => dragging=false);
  window.addEventListener('mousemove', e => {
    if (!dragging) return;
    const dx=e.clientX-lx, dy=e.clientY-ly; lx=e.clientX; ly=e.clientY;
    if (rightDrag) {
      const right = new THREE.Vector3().crossVectors(camera.getWorldDirection(new THREE.Vector3()), camera.up).normalize();
      target.addScaledVector(right, -dx*0.5);
      target.addScaledVector(camera.up, dy*0.5);
    } else {
      sph.theta -= dx*0.005;
      sph.phi = Math.max(0.05, Math.min(Math.PI-0.05, sph.phi + dy*0.005));
    }
    updateCam();
  });
  el.addEventListener('wheel', e => { sph.r = Math.max(100, sph.r + e.deltaY*0.5); updateCam(); });

  // Touch support
  let touches = [];
  el.addEventListener('touchstart', e => { touches = Array.from(e.touches); e.preventDefault(); }, {passive:false});
  el.addEventListener('touchmove', e => {
    if (e.touches.length === 1) {
      const t = e.touches[0], prev = touches[0];
      if (prev) {
        sph.theta -= (t.clientX - prev.clientX) * 0.005;
        sph.phi = Math.max(0.05, Math.min(Math.PI-0.05, sph.phi + (t.clientY - prev.clientY) * 0.005));
      }
    } else if (e.touches.length === 2) {
      const d0 = Math.hypot(touches[0].clientX-touches[1].clientX, touches[0].clientY-touches[1].clientY);
      const d1 = Math.hypot(e.touches[0].clientX-e.touches[1].clientX, e.touches[0].clientY-e.touches[1].clientY);
      sph.r = Math.max(100, sph.r * (d0/d1));
    }
    touches = Array.from(e.touches);
    updateCam();
    e.preventDefault();
  }, {passive:false});

  window.addEventListener('resize', () => {
    camera.aspect = canvas.clientWidth / canvas.clientHeight;
    camera.updateProjectionMatrix();
    renderer.setSize(canvas.clientWidth, canvas.clientHeight, false);
  });
  renderer.setSize(canvas.clientWidth, canvas.clientHeight, false);
  animate();
}

function animate() {
  requestAnimationFrame(animate);
  renderer.render(scene, camera);
}

// Color by normal direction (hue = angle)
function normalColor(n) {
  // Map normal sphere direction to hue
  const hue = (Math.atan2(n.z, n.x) / (Math.PI * 2) + 1) % 1;
  return new THREE.Color().setHSL(hue, 0.7, 0.55);
}

function renderScene(plates) {
  while (scene.children.length > 2) scene.remove(scene.children[scene.children.length-1]);
  scene.add(new THREE.AxesHelper(80));

  const r = +document.getElementById('targetRadius').value;
  scene.add(new THREE.Mesh(
    new THREE.SphereGeometry(r, 32, 20),
    new THREE.MeshBasicMaterial({ color: 0x223344, wireframe: true, transparent:true, opacity:0.1 })
  ));

  plates.forEach(p => {
    const col = normalColor(p.normal);
    const mat = new THREE.MeshLambertMaterial({ color: col, transparent:true, opacity:0.72, side:THREE.DoubleSide });
    const geo = new THREE.BoxGeometry(p.size, p.size, p.thick);
    const mesh = new THREE.Mesh(geo, mat);
    mesh.position.copy(p.center);
    mesh.quaternion.setFromUnitVectors(new THREE.Vector3(0,0,1), new THREE.Vector3(p.normal.x, p.normal.y, p.normal.z));
    scene.add(mesh);

    // Slit visualization (yellow lines)
    p.slits.forEach(s => {
      const wEntry = p.localToWorld(s.entry.u, s.entry.v, 0);
      const wExit  = p.localToWorld(s.exit.u,  s.exit.v,  0);
      const geo2 = new THREE.BufferGeometry().setFromPoints([
        new THREE.Vector3(wEntry.x, wEntry.y, wEntry.z),
        new THREE.Vector3(wExit.x,  wExit.y,  wExit.z)
      ]);
      scene.add(new THREE.Line(geo2, new THREE.LineBasicMaterial({ color: 0xffff00, linewidth: 2 })));
    });
  });
}

// ============================================================
// CSV Export
// ============================================================
function exportCSV() {
  if (!PLATES.length) { alert('Run optimization first'); return; }
  const rows = ['id,cx,cy,cz,nx,ny,nz,num_slits'];
  PLATES.forEach((p, i) => {
    rows.push([i, p.center.x.toFixed(2), p.center.y.toFixed(2), p.center.z.toFixed(2),
      p.normal.x.toFixed(4), p.normal.y.toFixed(4), p.normal.z.toFixed(4), p.slits.length].join(','));
  });
  rows.push('');
  rows.push('plate_id,slit_idx,other_id,entry_u,entry_v,exit_u,exit_v,width');
  PLATES.forEach((p, i) => {
    p.slits.forEach((s, si) => {
      rows.push([i, si, s.inserted.id,
        s.entry.u.toFixed(2), s.entry.v.toFixed(2),
        s.exit.u.toFixed(2),  s.exit.v.toFixed(2),
        s.width.toFixed(3)].join(','));
    });
  });
  download('slit_plates.csv', rows.join('\n'), 'text/csv');
}

// ============================================================
// DXF Export (sorted by z-coordinate)
// ============================================================
function exportDXF() {
  if (!PLATES.length) { alert('Run optimization first'); return; }
  const cols    = +document.getElementById('dxfCols').value;
  const spacing = +document.getElementById('dxfSpacing').value;
  const size    = PLATES[0].size;

  const sorted = [...PLATES].sort((a, b) => b.center.z - a.center.z);
  let body = '';
  sorted.forEach((p, idx) => {
    const ox = (idx % cols) * (size + spacing);
    const oy = -Math.floor(idx / cols) * (size + spacing);
    const h = size / 2;

    body += dxfRect(ox-h, oy-h, ox+h, oy+h, 'PLATES');
    body += dxfText(ox-h+2, oy-h+2, String(idx+1), 'LABELS', size*0.08);

    p.slits.forEach(s => {
      const eu = s.entry.u + ox, ev = s.entry.v + oy;
      const xu = s.exit.u  + ox, xv = s.exit.v  + oy;
      const du = xu-eu, dv = xv-ev;
      const len = Math.sqrt(du*du+dv*dv);
      if (len < 1e-9) return;
      const hw = s.width/2;
      const nx = -dv/len*hw, ny = du/len*hw;
      body += dxfLine(eu+nx,ev+ny, xu+nx,xv+ny,'SLITS');
      body += dxfLine(xu+nx,xv+ny, xu-nx,xv-ny,'SLITS');
      body += dxfLine(xu-nx,xv-ny, eu-nx,ev-ny,'SLITS');
      body += dxfLine(eu-nx,ev-ny, eu+nx,ev+ny,'SLITS');
    });
  });
  const full = '0\nSECTION\n2\nHEADER\n9\n$INSUNITS\n70\n4\n0\nENDSEC\n0\nSECTION\n2\nENTITIES\n'
    + body + '0\nENDSEC\n0\nEOF\n';
  download('slit_plates.dxf', full, 'application/dxf');
}

function dxfRect(x1,y1,x2,y2,layer) {
  return dxfLine(x1,y1,x2,y1,layer)+dxfLine(x2,y1,x2,y2,layer)+
         dxfLine(x2,y2,x1,y2,layer)+dxfLine(x1,y2,x1,y1,layer);
}
function dxfLine(x1,y1,x2,y2,layer) {
  return `0\nLINE\n8\n${layer}\n10\n${x1.toFixed(4)}\n20\n${y1.toFixed(4)}\n30\n0\n11\n${x2.toFixed(4)}\n21\n${y2.toFixed(4)}\n31\n0\n`;
}
function dxfText(x,y,txt,layer,h) {
  return `0\nTEXT\n8\n${layer}\n10\n${x.toFixed(4)}\n20\n${y.toFixed(4)}\n30\n0\n40\n${h.toFixed(4)}\n1\n${txt}\n`;
}

// ============================================================
// Top View PNG
// ============================================================
function exportTopView() {
  if (!PLATES.length) { alert('Run optimization first'); return; }
  const sc   = +document.getElementById('topScale').value;
  const size = PLATES[0].size;
  const r    = +document.getElementById('targetRadius').value;
  const dim  = Math.ceil((r*2+size)*sc*1.15);

  const canvas = document.getElementById('topview-canvas');
  canvas.width = canvas.height = dim;
  const ctx = canvas.getContext('2d');
  ctx.fillStyle = '#1a1a2e';
  ctx.fillRect(0,0,dim,dim);
  const cx = dim/2, cy = dim/2;

  PLATES.forEach((p, i) => {
    const x = cx + p.center.x*sc, y = cy - p.center.z*sc;
    const h = size*sc/2;
    const c = normalColor(p.normal);
    ctx.fillStyle   = `rgba(${~~(c.r*255)},${~~(c.g*255)},${~~(c.b*255)},0.6)`;
    ctx.strokeStyle = `rgb(${~~(c.r*255)},${~~(c.g*255)},${~~(c.b*255)})`;
    ctx.lineWidth = 1;
    ctx.fillRect(x-h, y-h, h*2, h*2);
    ctx.strokeRect(x-h, y-h, h*2, h*2);
    ctx.fillStyle = '#fff';
    ctx.font = `${Math.max(8, h*0.4)}px monospace`;
    ctx.textAlign = 'center';
    ctx.textBaseline = 'middle';
    ctx.fillText(String(i+1), x, y);
  });

  canvas.toBlob(blob => {
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url; a.download = 'slit_topview.png'; a.click();
    URL.revokeObjectURL(url);
  });
}

// ============================================================
// Download helper
// ============================================================
function download(name, content, mime) {
  const blob = new Blob([content], { type: mime });
  const a = document.createElement('a');
  a.href = URL.createObjectURL(blob);
  a.download = name; a.click();
}

// ============================================================
// Init
// ============================================================
initRenderer();
