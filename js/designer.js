// ============================================================
// Slit Plate Designer — Core Engine
// ============================================================

const LOG = (msg) => {
  const el = document.getElementById('log');
  el.textContent += msg + '\n';
  el.scrollTop = el.scrollHeight;
};
const STAT = (id, val) => document.getElementById(id).textContent = val;

// ============================================================
// Math helpers
// ============================================================
const V3 = THREE.Vector3;

function fibonacciSphere(n) {
  const pts = [];
  const phi = Math.PI * (3 - Math.sqrt(5));
  for (let i = 0; i < n; i++) {
    const y = 1 - (i / (n - 1)) * 2;
    const r = Math.sqrt(1 - y * y);
    const theta = phi * i;
    pts.push(new V3(r * Math.cos(theta), y, r * Math.sin(theta)));
  }
  return pts;
}

function cylinderPoints(n, radius, height) {
  const pts = [];
  // side
  const nSide = Math.round(n * 0.8);
  for (let i = 0; i < nSide; i++) {
    const theta = (i / nSide) * Math.PI * 2;
    const y = (Math.random() - 0.5) * height;
    pts.push(new V3(radius * Math.cos(theta), y, radius * Math.sin(theta)));
  }
  // caps
  for (let i = pts.length; i < n; i++) {
    const r = radius * Math.sqrt(Math.random());
    const theta = Math.random() * Math.PI * 2;
    const y = (Math.random() < 0.5 ? -1 : 1) * height / 2;
    pts.push(new V3(r * Math.cos(theta), y, r * Math.sin(theta)));
  }
  return pts;
}

// ============================================================
// Plate class
// ============================================================
class Plate {
  constructor(id, center, normal, size, thickness) {
    this.id = id;
    this.center = center.clone();
    this.normal = normal.clone().normalize();
    this.size = size;      // side length
    this.thick = thickness;
    this.slits = [];       // Slit objects
    this.neighbors = [];   // connected plate ids

    // Build local axes: tangent1, tangent2 ⊥ normal
    const up = Math.abs(this.normal.y) < 0.9 ? new V3(0, 1, 0) : new V3(1, 0, 0);
    this.u = new V3().crossVectors(this.normal, up).normalize();
    this.v = new V3().crossVectors(this.normal, this.u).normalize();
  }

  // World position from local (u, v) coords (center = origin)
  localToWorld(pu, pv) {
    return new V3()
      .addScaledVector(this.u, pu)
      .addScaledVector(this.v, pv)
      .add(this.center);
  }

  // Project world point onto plate local coords
  worldToLocal(pt) {
    const d = new V3().subVectors(pt, this.center);
    return { u: d.dot(this.u), v: d.dot(this.v) };
  }

  // Is local point inside plate boundary?
  containsLocal(pu, pv, margin = 0) {
    const half = this.size / 2 - margin;
    return Math.abs(pu) <= half && Math.abs(pv) <= half;
  }

  // Corners in world coords
  corners() {
    const h = this.size / 2;
    return [
      this.localToWorld(-h, -h),
      this.localToWorld(h, -h),
      this.localToWorld(h, h),
      this.localToWorld(-h, h),
    ];
  }
}

// ============================================================
// Slit class
// ============================================================
class Slit {
  constructor(plate, otherPlate, entry, exit, width) {
    this.plate = plate;           // Plate this slit belongs to
    this.otherPlate = otherPlate; // Plate that inserts through this slit
    // entry and exit are local (u,v) coords on this.plate
    this.entry = entry;  // {u, v} — on edge
    this.exit = exit;    // {u, v} — interior
    this.width = width;  // = thickness of otherPlate + tolerance
  }

  // Check if two slits on the same plate overlap
  overlapsWith(other) {
    // Represent each slit as a line segment in local UV space
    // Check bounding box overlap with width expansion
    const expand = Math.max(this.width, other.width) / 2;
    const a0 = { u: this.entry.u, v: this.entry.v };
    const a1 = { u: this.exit.u, v: this.exit.v };
    const b0 = { u: other.entry.u, v: other.entry.v };
    const b1 = { u: other.exit.u, v: other.exit.v };
    return segmentsOverlap2D(a0, a1, b0, b1, expand);
  }
}

function segmentsOverlap2D(a0, a1, b0, b1, expand) {
  // AABB check first
  const minAu = Math.min(a0.u, a1.u) - expand, maxAu = Math.max(a0.u, a1.u) + expand;
  const minAv = Math.min(a0.v, a1.v) - expand, maxAv = Math.max(a0.v, a1.v) + expand;
  const minBu = Math.min(b0.u, b1.u) - expand, maxBu = Math.max(b0.u, b1.u) + expand;
  const minBv = Math.min(b0.v, b1.v) - expand, maxBv = Math.max(b0.v, b1.v) + expand;
  return !(maxAu < minBu || maxBu < minAu || maxAv < minBv || maxBv < minAv);
}

// ============================================================
// Compute slit geometry between two perpendicular plates
// Returns {slitA, slitB} or null if no valid intersection
// ============================================================
function computeSlits(pA, pB, tol) {
  // Intersection line of the two infinite planes
  const lineDir = new V3().crossVectors(pA.normal, pB.normal).normalize();
  if (lineDir.length() < 0.01) return null; // parallel

  // Find a point on the intersection line
  // Solve: pA.normal·(P - pA.center)=0 and pB.normal·(P - pB.center)=0
  // Using parametric approach: P = pA.center + t*(pA.normal × lineDir) + s*(lineDir)
  // Simple: find point nearest to both centers on intersection line
  const dA = pA.normal.dot(pA.center);
  const dB = pB.normal.dot(pB.center);
  const n1n2 = pA.normal.dot(pB.normal); // should ≈ 0
  const det = 1 - n1n2 * n1n2;
  if (Math.abs(det) < 1e-6) return null;
  const c1 = (dA - n1n2 * dB) / det;
  const c2 = (dB - n1n2 * dA) / det;
  const linePoint = new V3()
    .addScaledVector(pA.normal, c1)
    .addScaledVector(pB.normal, c2);

  // Parameterize intersection line: P(t) = linePoint + t * lineDir
  // Find overlap of the two plates along this line
  // Project plate A boundary onto line
  const half = Math.min(pA.size, pB.size) / 2;
  const tRangeA = projectPlateOnLine(pA, linePoint, lineDir);
  const tRangeB = projectPlateOnLine(pB, linePoint, lineDir);
  if (!tRangeA || !tRangeB) return null;

  const tMin = Math.max(tRangeA[0], tRangeB[0]);
  const tMax = Math.min(tRangeA[1], tRangeB[1]);
  if (tMax - tMin < pA.thick * 2) return null;

  // Intersection segment midpoint
  const tMid = (tMin + tMax) / 2;

  // Slit on plate A (pB passes through pA)
  // The slit in pA runs along lineDir projected onto pA's plane
  // Entry point: where pB's center plane intersects pA's edge
  const slitA = buildSlit(pA, pB, linePoint, lineDir, tMin, tMax, tol);
  const slitB = buildSlit(pB, pA, linePoint, lineDir, tMin, tMax, tol);

  if (!slitA || !slitB) return null;
  return { slitA, slitB };
}

function projectPlateOnLine(plate, linePoint, lineDir) {
  const corners = plate.corners();
  const ts = corners.map(c => new V3().subVectors(c, linePoint).dot(lineDir));
  const tMin = Math.min(...ts);
  const tMax = Math.max(...ts);
  // Also check that the line actually passes through the plate
  const mid = new V3().copy(linePoint).addScaledVector(lineDir, (tMin + tMax) / 2);
  const loc = plate.worldToLocal(mid);
  if (!plate.containsLocal(loc.u, loc.v, plate.size * 0.05)) return null;
  return [tMin, tMax];
}

function buildSlit(hostPlate, insertedPlate, linePoint, lineDir, tMin, tMax, tol) {
  const half = hostPlate.size / 2;
  // Project line segment endpoints onto hostPlate local coords
  const wEntry = new V3().copy(linePoint).addScaledVector(lineDir, tMin);
  const wExit = new V3().copy(linePoint).addScaledVector(lineDir, tMax);
  const lEntry = hostPlate.worldToLocal(wEntry);
  const lExit = hostPlate.worldToLocal(wExit);

  // Clamp to plate bounds
  function clampLocal(lp) {
    return {
      u: Math.max(-half, Math.min(half, lp.u)),
      v: Math.max(-half, Math.min(half, lp.v))
    };
  }
  const cEntry = clampLocal(lEntry);
  const cExit = clampLocal(lExit);

  // Slit width = thickness of inserted plate * tolerance
  const slitWidth = insertedPlate.thick * tol;

  // Check that slit length > slitWidth
  const du = cExit.u - cEntry.u, dv = cExit.v - cEntry.v;
  const len = Math.sqrt(du * du + dv * dv);
  if (len < slitWidth * 2) return null;

  // The entry end should be on the edge, exit in interior
  // Determine which end is closer to edge
  function distToEdge(lp) {
    return half - Math.max(Math.abs(lp.u), Math.abs(lp.v));
  }
  let entry, exit;
  if (distToEdge(cEntry) < distToEdge(cExit)) {
    // Snap entry to edge
    entry = snapToEdge(cEntry, cExit, half);
    exit = cExit;
  } else {
    entry = snapToEdge(cExit, cEntry, half);
    exit = cEntry;
  }

  return new Slit(hostPlate, insertedPlate, entry, exit, slitWidth);
}

function snapToEdge(pt, other, half) {
  // Move pt to nearest edge while keeping direction toward other
  const du = other.u - pt.u, dv = other.v - pt.v;
  const len = Math.sqrt(du * du + dv * dv);
  if (len < 1e-9) return { u: half, v: 0 };

  // Find where line from pt toward other hits the plate boundary
  let t = Infinity;
  if (Math.abs(du) > 1e-9) {
    const tx1 = (half - pt.u) / du;
    const tx2 = (-half - pt.u) / du;
    if (tx1 > 0) t = Math.min(t, tx1);
    if (tx2 > 0) t = Math.min(t, tx2);
  }
  if (Math.abs(dv) > 1e-9) {
    const tv1 = (half - pt.v) / dv;
    const tv2 = (-half - pt.v) / dv;
    if (tv1 > 0) t = Math.min(t, tv1);
    if (tv2 > 0) t = Math.min(t, tv2);
  }
  if (!isFinite(t)) return pt;
  return { u: pt.u + du * t, v: pt.v + dv * t };
}

// ============================================================
// Connectivity check (BFS)
// ============================================================
function checkConnectivity(plates) {
  if (plates.length === 0) return true;
  const visited = new Set();
  const queue = [plates[0].id];
  visited.add(plates[0].id);
  const adjMap = new Map(plates.map(p => [p.id, p.neighbors]));
  while (queue.length > 0) {
    const id = queue.shift();
    for (const nid of (adjMap.get(id) || [])) {
      if (!visited.has(nid)) { visited.add(nid); queue.push(nid); }
    }
  }
  return visited.size === plates.size || visited.size === plates.length;
}

// ============================================================
// Main optimizer
// ============================================================
let PLATES = [];
let PAIRS = [];

async function runOptimize() {
  const size = parseFloat(document.getElementById('plateSize').value);
  const thick = parseFloat(document.getElementById('plateThick').value);
  const radius = parseFloat(document.getElementById('targetRadius').value);
  const shape = document.getElementById('targetShape').value;
  const density = parseInt(document.getElementById('density').value);
  const iters = parseInt(document.getElementById('iterations').value);
  const slitTol = parseFloat(document.getElementById('slitTol').value);
  const cylH = parseFloat(document.getElementById('cylHeight').value);

  document.getElementById('log').textContent = '';
  LOG('Starting optimization...');

  // 1. Generate initial plate centers on target surface
  let pts;
  if (shape === 'sphere' || shape === 'hemisphere') {
    pts = fibonacciSphere(shape === 'hemisphere' ? density * 2 : density);
    if (shape === 'hemisphere') pts = pts.filter(p => p.y >= -0.1);
    pts.forEach(p => p.multiplyScalar(radius));
  } else {
    pts = cylinderPoints(density, radius, cylH);
  }

  // 2. Assign normals pointing outward from shape center
  const plates = pts.map((p, i) => {
    const normal = p.clone().normalize();
    return new Plate(i, p, normal, size, thick);
  });

  // 3. Snap normals to nearest axis-aligned pair
  // For slit joints, we discretize normals to one of 3 axis sets
  // We use a simplified approach: assign each plate to X, Y, or Z dominant direction
  // and align normal to one of 6 principal directions + 45° diagonals
  // Actually for true perpendicularity we group plates into 3 families:
  // Family 0: normal mostly along X → set normal to X
  // Family 1: normal mostly along Y → set normal to Y
  // Family 2: normal mostly along Z → set normal to Z
  // This is a simplified approach — real optimization would allow arbitrary orientations
  // as long as connected pairs are perpendicular.
  // For now, we use axis-aligned approach for valid slit joints.
  plates.forEach(p => {
    const n = p.normal;
    const ax = Math.abs(n.x), ay = Math.abs(n.y), az = Math.abs(n.z);
    if (ax >= ay && ax >= az) {
      p.normal.set(n.x > 0 ? 1 : -1, 0, 0);
    } else if (ay >= ax && ay >= az) {
      p.normal.set(0, n.y > 0 ? 1 : -1, 0);
    } else {
      p.normal.set(0, 0, n.z > 0 ? 1 : -1);
    }
    // Rebuild local axes
    const up = Math.abs(p.normal.y) < 0.9 ? new V3(0, 1, 0) : new V3(1, 0, 0);
    p.u = new V3().crossVectors(p.normal, up).normalize();
    p.v = new V3().crossVectors(p.normal, p.u).normalize();
  });

  LOG(`Generated ${plates.length} plates`);

  // 4. Iterative optimization: move plates toward target surface
  for (let iter = 0; iter < iters; iter++) {
    plates.forEach(p => {
      // Project center back onto target surface
      if (shape === 'sphere') {
        p.center.setLength(radius);
      } else if (shape === 'hemisphere') {
        p.center.setLength(radius);
        if (p.center.y < 0) p.center.y = 0;
        p.center.setLength(radius);
      } else {
        // cylinder: project onto cylinder
        const r = Math.sqrt(p.center.x * p.center.x + p.center.z * p.center.z);
        if (r > 1e-9) {
          p.center.x = p.center.x / r * radius;
          p.center.z = p.center.z / r * radius;
        }
        p.center.y = Math.max(-cylH / 2, Math.min(cylH / 2, p.center.y));
      }

      // Repulsion from neighbors to avoid overlap
      plates.forEach(q => {
        if (q.id === p.id) return;
        const d = new V3().subVectors(p.center, q.center);
        const dist = d.length();
        const minDist = size * 0.7;
        if (dist < minDist && dist > 1e-9) {
          const push = d.normalize().multiplyScalar((minDist - dist) * 0.1);
          p.center.add(push);
        }
      });
    });
  }
  LOG('Optimization done');

  // 5. Find pairs of perpendicular plates that are close enough to intersect
  const pairs = [];
  for (let i = 0; i < plates.length; i++) {
    for (let j = i + 1; j < plates.length; j++) {
      const pA = plates[i], pB = plates[j];
      // Must be perpendicular (dot product ≈ 0)
      if (Math.abs(pA.normal.dot(pB.normal)) > 0.05) continue;
      // Must be close enough
      const dist = pA.center.distanceTo(pB.center);
      if (dist > size * 1.2) continue;
      // Compute slit geometry
      const result = computeSlits(pA, pB, slitTol);
      if (!result) continue;
      const { slitA, slitB } = result;
      // Check no overlap with existing slits
      let ok = true;
      for (const s of pA.slits) { if (s.overlapsWith(slitA)) { ok = false; break; } }
      if (ok) for (const s of pB.slits) { if (s.overlapsWith(slitB)) { ok = false; break; } }
      if (!ok) continue;
      pA.slits.push(slitA);
      pB.slits.push(slitB);
      pA.neighbors.push(pB.id);
      pB.neighbors.push(pA.id);
      pairs.push([i, j]);
    }
  }
  LOG(`Found ${pairs.length} slit connections`);

  // 6. Remove disconnected plates (keep largest connected component)
  const visitedSet = new Set();
  let bestComp = [];
  plates.forEach(p => {
    if (visitedSet.has(p.id)) return;
    const comp = [];
    const q = [p.id];
    const idMap = new Map(plates.map(x => [x.id, x]));
    while (q.length) {
      const id = q.shift();
      if (visitedSet.has(id)) continue;
      visitedSet.add(id);
      comp.push(id);
      (idMap.get(id)?.neighbors || []).forEach(nid => { if (!visitedSet.has(nid)) q.push(nid); });
    }
    if (comp.length > bestComp.length) bestComp = comp;
  });
  const bestSet = new Set(bestComp);
  const finalPlates = plates.filter(p => bestSet.has(p.id));
  // Re-number slits
  finalPlates.forEach(p => {
    p.slits = p.slits.filter(s => bestSet.has(s.otherPlate.id));
  });
  LOG(`Connected component: ${finalPlates.length} plates`);

  PLATES = finalPlates;
  PAIRS = pairs.filter(([i, j]) => bestSet.has(i) && bestSet.has(j));

  // Update stats
  STAT('st-plates', finalPlates.length);
  STAT('st-slits', finalPlates.reduce((acc, p) => acc + p.slits.length, 0));
  STAT('st-connected', bestComp.length === plates.length ? '✓ All' : `${bestComp.length}/${plates.length}`);
  const coverage = (finalPlates.length / pts.length * 100).toFixed(1);
  STAT('st-coverage', coverage + '%');

  LOG('Rendering...');
  renderScene(finalPlates);
  LOG('Done.');
}

// ============================================================
// Three.js rendering
// ============================================================
let scene, camera, renderer, controls;

function initRenderer() {
  const canvas = document.getElementById('canvas3d');
  renderer = new THREE.WebGLRenderer({ canvas, antialias: true, alpha: true });
  renderer.setPixelRatio(window.devicePixelRatio);
  renderer.setClearColor(0x1a1a2e);

  scene = new THREE.Scene();
  camera = new THREE.PerspectiveCamera(60, canvas.clientWidth / canvas.clientHeight, 1, 10000);
  camera.position.set(0, 200, 600);

  // Lights
  const amb = new THREE.AmbientLight(0xffffff, 0.4);
  scene.add(amb);
  const dir = new THREE.DirectionalLight(0xffffff, 0.8);
  dir.position.set(1, 2, 1);
  scene.add(dir);

  // Simple orbit controls
  let isDragging = false, isRightDrag = false;
  let lastX = 0, lastY = 0;
  let spherical = { theta: 0.3, phi: 1.0, r: 700 };
  let target = new THREE.Vector3(0, 0, 0);

  function updateCamera() {
    camera.position.set(
      target.x + spherical.r * Math.sin(spherical.phi) * Math.sin(spherical.theta),
      target.y + spherical.r * Math.cos(spherical.phi),
      target.z + spherical.r * Math.sin(spherical.phi) * Math.cos(spherical.theta)
    );
    camera.lookAt(target);
  }
  updateCamera();

  canvas.addEventListener('mousedown', e => {
    isDragging = true; isRightDrag = e.button === 2;
    lastX = e.clientX; lastY = e.clientY;
    e.preventDefault();
  });
  canvas.addEventListener('contextmenu', e => e.preventDefault());
  window.addEventListener('mouseup', () => isDragging = false);
  window.addEventListener('mousemove', e => {
    if (!isDragging) return;
    const dx = e.clientX - lastX, dy = e.clientY - lastY;
    lastX = e.clientX; lastY = e.clientY;
    if (isRightDrag) {
      const right = new THREE.Vector3().crossVectors(camera.getWorldDirection(new THREE.Vector3()), camera.up).normalize();
      target.addScaledVector(right, -dx * 0.5);
      target.addScaledVector(camera.up, dy * 0.5);
    } else {
      spherical.theta -= dx * 0.005;
      spherical.phi = Math.max(0.1, Math.min(Math.PI - 0.1, spherical.phi + dy * 0.005));
    }
    updateCamera();
  });
  canvas.addEventListener('wheel', e => {
    spherical.r = Math.max(100, spherical.r + e.deltaY * 0.5);
    updateCamera();
  });

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

// Color palette for plate families
const FAMILY_COLORS = [0x4fc3f7, 0xf48fb1, 0xa5d6a7, 0xffe082, 0xce93d8];

function getFamilyColor(plate) {
  const n = plate.normal;
  if (Math.abs(n.x) > 0.9) return FAMILY_COLORS[0];
  if (Math.abs(n.y) > 0.9) return FAMILY_COLORS[1];
  return FAMILY_COLORS[2];
}

function renderScene(plates) {
  // Clear previous meshes
  while (scene.children.length > 2) scene.remove(scene.children[scene.children.length - 1]);

  // Add axis helper
  scene.add(new THREE.AxesHelper(100));

  const plateMats = [0, 1, 2].map(i => new THREE.MeshLambertMaterial({
    color: FAMILY_COLORS[i], transparent: true, opacity: 0.75, side: THREE.DoubleSide
  }));

  plates.forEach(p => {
    const geo = new THREE.PlaneGeometry(p.size, p.size);
    const matIdx = Math.abs(p.normal.x) > 0.9 ? 0 : Math.abs(p.normal.y) > 0.9 ? 1 : 2;
    const mesh = new THREE.Mesh(geo, plateMats[matIdx]);
    mesh.position.copy(p.center);
    // Orient plane to face along normal
    mesh.quaternion.setFromUnitVectors(new THREE.Vector3(0, 0, 1), p.normal);
    scene.add(mesh);

    // Draw slit outlines
    p.slits.forEach(slit => {
      const e = slit.entry, x = slit.exit;
      const hw = slit.width / 2;
      // Draw slit as a thin yellow box
      const seg = new THREE.Vector2(x.u - e.u, x.v - e.v);
      const len = seg.length();
      const slitGeo = new THREE.PlaneGeometry(hw * 2, len);
      const slitMesh = new THREE.Mesh(slitGeo, new THREE.MeshBasicMaterial({ color: 0xffff00, side: THREE.DoubleSide }));
      const mid = p.localToWorld((e.u + x.u) / 2, (e.v + x.v) / 2);
      slitMesh.position.copy(mid);
      slitMesh.quaternion.setFromUnitVectors(new THREE.Vector3(0, 0, 1), p.normal);
      const angle = Math.atan2(seg.x, seg.y);
      slitMesh.rotateZ(angle);
      scene.add(slitMesh);
    });
  });

  // Draw center point of target shape as a wireframe sphere
  const r = parseFloat(document.getElementById('targetRadius').value);
  const wf = new THREE.Mesh(
    new THREE.SphereGeometry(r, 24, 16),
    new THREE.MeshBasicMaterial({ color: 0x334455, wireframe: true, transparent: true, opacity: 0.15 })
  );
  scene.add(wf);
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
  // Slit details
  rows.push('');
  rows.push('plate_id,slit_idx,other_plate_id,entry_u,entry_v,exit_u,exit_v,width');
  PLATES.forEach((p, i) => {
    p.slits.forEach((s, si) => {
      rows.push([i, si, s.otherPlate.id,
        s.entry.u.toFixed(2), s.entry.v.toFixed(2), s.exit.u.toFixed(2), s.exit.v.toFixed(2),
        s.width.toFixed(3)].join(','));
    });
  });
  download('slit_plates.csv', rows.join('\n'), 'text/csv');
}

// ============================================================
// DXF Export
// ============================================================
function exportDXF() {
  if (!PLATES.length) { alert('Run optimization first'); return; }
  const cols = parseInt(document.getElementById('dxfCols').value);
  const spacing = parseFloat(document.getElementById('dxfSpacing').value);
  const size = PLATES[0].size;
  const thick = PLATES[0].thick;

  // Sort plates by center.z descending (top-down assembly order)
  const sorted = [...PLATES].sort((a, b) => b.center.z - a.center.z);

  let dxf = '';

  sorted.forEach((p, idx) => {
    const col = idx % cols;
    const row = Math.floor(idx / cols);
    const ox = col * (size + spacing);
    const oy = -row * (size + spacing);
    const half = size / 2;

    // Plate outline
    dxf += dxfRect(ox - half, oy - half, ox + half, oy + half, 'PLATES');

    // Slits
    p.slits.forEach(slit => {
      const eu = slit.entry.u + ox, ev = slit.entry.v + oy;
      const xu = slit.exit.u + ox, xv = slit.exit.v + oy;
      const hw = slit.width / 2;
      // Perpendicular direction to slit line
      const du = xu - eu, dv = xv - ev;
      const len = Math.sqrt(du * du + dv * dv);
      if (len < 1e-9) return;
      const nx = -dv / len * hw, ny = du / len * hw;
      // 4-sided slit polygon (as 4 lines)
      dxf += dxfLine(eu + nx, ev + ny, xu + nx, xv + ny, 'SLITS');
      dxf += dxfLine(xu + nx, xv + ny, xu - nx, xv - ny, 'SLITS');
      dxf += dxfLine(xu - nx, xv - ny, eu - nx, ev - ny, 'SLITS');
      dxf += dxfLine(eu - nx, ev - ny, eu + nx, ev + ny, 'SLITS');
    });

    // Plate number label (as TEXT entity)
    dxf += dxfText(ox - half + 2, oy - half + 2, String(idx + 1), 'LABELS', size * 0.08);
  });

  dxf += 'ENDSEC\n0\nEOF\n';
  download('slit_plates.dxf', dxfHeader() + dxf, 'application/dxf');
}

function dxfHeader() {
  return `0\nSECTION\n2\nHEADER\n9\n$INSUNITS\n70\n4\n0\nENDSEC\n0\nSECTION\n2\nENTITIES\n`;
}

function dxfRect(x1, y1, x2, y2, layer) {
  return dxfLine(x1, y1, x2, y1, layer) + dxfLine(x2, y1, x2, y2, layer) +
    dxfLine(x2, y2, x1, y2, layer) + dxfLine(x1, y2, x1, y1, layer);
}

function dxfLine(x1, y1, x2, y2, layer) {
  return `0\nLINE\n8\n${layer}\n10\n${x1.toFixed(4)}\n20\n${y1.toFixed(4)}\n30\n0.0\n11\n${x2.toFixed(4)}\n21\n${y2.toFixed(4)}\n31\n0.0\n`;
}

function dxfText(x, y, txt, layer, h) {
  return `0\nTEXT\n8\n${layer}\n10\n${x.toFixed(4)}\n20\n${y.toFixed(4)}\n30\n0.0\n40\n${h.toFixed(4)}\n1\n${txt}\n`;
}

// ============================================================
// Top view PNG Export
// ============================================================
function exportTopView() {
  if (!PLATES.length) { alert('Run optimization first'); return; }
  const scale = parseFloat(document.getElementById('topScale').value);
  const size = PLATES[0].size;
  const r = parseFloat(document.getElementById('targetRadius').value);
  const dim = Math.ceil((r * 2 + size) * scale * 1.1);

  const canvas = document.getElementById('topview-canvas');
  canvas.width = dim;
  canvas.height = dim;
  const ctx = canvas.getContext('2d');
  ctx.fillStyle = '#1a1a2e';
  ctx.fillRect(0, 0, dim, dim);

  const cx = dim / 2, cy = dim / 2;

  PLATES.forEach((p, idx) => {
    const x = cx + p.center.x * scale;
    const y = cy - p.center.z * scale;
    const half = size * scale / 2;

    // Color by family
    const col = Math.abs(p.normal.x) > 0.9 ? '#4fc3f7' : Math.abs(p.normal.y) > 0.9 ? '#f48fb1' : '#a5d6a7';
    ctx.fillStyle = col + 'aa';
    ctx.strokeStyle = col;
    ctx.lineWidth = 1;
    ctx.fillRect(x - half, y - half, half * 2, half * 2);
    ctx.strokeRect(x - half, y - half, half * 2, half * 2);

    // Number
    ctx.fillStyle = '#ffffff';
    ctx.font = `${Math.max(8, size * scale * 0.2)}px monospace`;
    ctx.textAlign = 'center';
    ctx.fillText(String(idx + 1), x, y + 4);
  });

  canvas.toBlob(blob => {
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url; a.download = 'slit_plates_topview.png'; a.click();
    URL.revokeObjectURL(url);
  });
}

// ============================================================
// Download helper
// ============================================================
function download(filename, content, mime) {
  const blob = new Blob([content], { type: mime });
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url; a.download = filename; a.click();
  URL.revokeObjectURL(url);
}

// ============================================================
// Init
// ============================================================
initRenderer();
