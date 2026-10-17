// Native-vector sample of the critical conditioned DHL four-colour process.
// Run with Node.js; optional first argument is the repository's absolute path.
// Sampling: independent Bernoulli(p_c) indicators, rejected until the crossing
// state matches the live parent; black interiors are deliberately unrevealed.
const fs = require('node:fs');
const path = require('node:path');
const repo = process.argv[2] || path.resolve(__dirname, '..');
const output = path.join(repo, 'figure/random_DHL-realisation-corrected.tex');
const auditOutput = path.join(__dirname, 'four-colour-realisation-audit.json');
const seed = 20261017;
let randomState = seed >>> 0;
function random() {
  randomState = (randomState + 0x6D2B79F5) >>> 0;
  let value = randomState;
  value = Math.imul(value ^ value >>> 15, value | 1);
  value ^= value + Math.imul(value ^ value >>> 7, value | 61);
  return ((value ^ value >>> 14) >>> 0) / 4294967296;
}
const p = (Math.sqrt(5) - 1) / 2;
const vertices = [{x: -0.5, y: 0}, {x: 0.5, y: 0}];
const generations = [[{tail: 0, head: 1, colour: 'red', active: [0, 1]}]];
const transitions = [];
const childPositions = [[0, 1], [1, 3], [0, 2], [2, 3]];
// Decreasing angles leave disjoint wedges at old high-degree vertices.
const offsets = [0.29, 0.125, 0.055];
for (let depth = 0; depth < 3; depth++) {
  const next = [];
  for (const [parentIndex, parent] of generations[depth].entries()) {
    const a = vertices[parent.tail], b = vertices[parent.head];
    const dx = b.x - a.x, dy = b.y - a.y;
    const top = vertices.length;
    vertices.push({x: (a.x + b.x) / 2 - offsets[depth] * dy,
                   y: (a.y + b.y) / 2 + offsets[depth] * dx});
    const bottom = vertices.length;
    vertices.push({x: (a.x + b.x) / 2 + offsets[depth] * dy,
                   y: (a.y + b.y) / 2 - offsets[depth] * dx});
    const ids = [parent.tail, top, bottom, parent.head];
    let indicators = null;
    if (parent.colour !== 'black') {
      do {
        indicators = childPositions.map(() => random() < p);
      } while (((indicators[0] && indicators[1]) ||
                (indicators[2] && indicators[3])) !== (parent.colour === 'red'));
    }
    const active = new Set(parent.colour === 'black' ? [] :
      parent.colour === 'green' ? [0] : [0, 3]);
    let changed = true;
    while (changed) {
      changed = false;
      childPositions.forEach(([u, v], index) => {
        if (indicators && indicators[index] && (active.has(u) || active.has(v))) {
          if (!active.has(u) || !active.has(v)) changed = true;
          active.add(u); active.add(v);
        }
      });
    }
    const first = next.length;
    childPositions.forEach(([u, v], index) => {
      const retained = [u, v].filter(endpoint => active.has(endpoint));
      const colour = retained.length === 0 ? 'black' :
        indicators[index] ? 'red' : retained.length === 2 ? 'blue' : 'green';
      // For green, parent.tail is active; propagation decides each child tail.
      const reverse = colour === 'green' && !active.has(u);
      next.push({tail: ids[reverse ? v : u], head: ids[reverse ? u : v], colour,
        active: retained.map(endpoint => ids[endpoint]), parent: parentIndex});
    });
    transitions.push({generation: depth + 1, parent: parentIndex,
      parentColour: parent.colour, parentTail: parent.tail, parentHead: parent.head,
      childVertices: ids, indicators, activeVertices: [...active].map(i => ids[i]),
      firstChild: first, numberOfChildren: 4});
  }
  generations.push(next);
}

function assert(condition, message) { if (!condition) throw new Error(message); }
const checks = [];
for (let depth = 0; depth < generations.length; depth++) {
  const edges = generations[depth];
  assert(edges.length === 4 ** depth, `Wrong edge count at ${depth}`);
  const redComponent = new Set([0]);
  let changed = true;
  while (changed) {
    changed = false;
    for (const edge of edges.filter(edge => edge.colour === 'red')) {
      if (redComponent.has(edge.tail) || redComponent.has(edge.head)) {
        if (!redComponent.has(edge.tail) || !redComponent.has(edge.head)) changed = true;
        redComponent.add(edge.tail); redComponent.add(edge.head);
      }
    }
  }
  assert(redComponent.has(1), `Roots not connected at ${depth}`);
  for (const edge of edges) {
    const retained = [edge.tail, edge.head].filter(v => redComponent.has(v));
    assert(retained.length === edge.active.length && retained.every(v => edge.active.includes(v)),
      `Global/local active mismatch at ${depth}`);
    if (edge.colour === 'red') assert(retained.length === 2, 'Detached red edge');
    if (edge.colour === 'blue') assert(retained.length === 2, 'Blue endpoint inactive');
    if (edge.colour === 'green') assert(redComponent.has(edge.tail) && !redComponent.has(edge.head),
      'Green arrow does not point active to inactive');
    if (edge.colour === 'black') assert(retained.length === 0, 'Black endpoint active');
  }
  checks.push({generation: depth, edges: edges.length, redVertices: redComponent.size,
    colours: Object.fromEntries(['red', 'blue', 'green', 'black'].map(colour =>
      [colour, edges.filter(e => e.colour === colour).length])),
    rootsConnected: true, allRedEdgesInRootComponent: true,
    allGreenArrowsActiveToInactive: true, allBlueEndpointsActive: true,
    allBlackEndpointsInactive: true});
}
for (const transition of transitions) {
  const parent = generations[transition.generation - 1][transition.parent];
  const children = generations[transition.generation].slice(transition.firstChild, transition.firstChild + 4);
  assert(new Set(transition.childVertices).size === 4, 'Non-private replacement interior');
  if (parent.colour === 'black') assert(children.every(child => child.colour === 'black'), 'Cemetery escape');
  else {
    const b = transition.indicators;
    assert(((b[0] && b[1]) || (b[2] && b[3])) === (parent.colour === 'red'), 'Conditioning error');
  }
}

// Count proper segment crossings, excluding shared vertices. This checks the
// drawing as well as graph combinatorics; all replacement interiors are private.
function cross(a, b, c) { return (b.x - a.x)*(c.y - a.y) - (b.y - a.y)*(c.x - a.x); }
for (const [depth, edges] of generations.entries()) {
  let crossings = 0;
  for (let i = 0; i < edges.length; i++) for (let j = 0; j < i; j++) {
    const e = edges[i], f = edges[j];
    if ([e.tail, e.head].some(v => v === f.tail || v === f.head)) continue;
    const a = vertices[e.tail], b = vertices[e.head], c = vertices[f.tail], d = vertices[f.head];
    if (cross(a,b,c)*cross(a,b,d) < -1e-15 && cross(c,d,a)*cross(c,d,b) < -1e-15) crossings++;
  }
  checks[depth].properEdgeCrossings = crossings;
  assert(crossings === 0, `Embedding crossings at ${depth}`);
}
const panels = [{centre: 0.8, width: 1.2}, {centre: 3.2, width: 2},
  {centre: 7, width: 3.2}, {centre: 12.5, width: 5.3}];
const f = value => value.toFixed(5);
const tex = [
  '% Generated by generate-four-colour-realisation.cjs; seed 20261017.',
  '% Correct conditional sample; every green arrow points active to inactive.',
  '\\begin{tikzpicture}[x=1cm,y=1cm,>=stealth,font=\\small,',
  '  sampleedge/.style={line width=.53pt,->,shorten >=1pt,shorten <=1pt},',
  '  samplevertex/.style={circle,fill=black,inner sep=0pt,minimum size=2.4pt}]',
  '\\path[use as bounding box] (0,-2.02) rectangle (15.6,1.68);',
];
const colours = {red: 'red', blue: 'blue!65', green: 'green!60!black', black: 'black!60'};
for (let depth = 0; depth < generations.length; depth++) {
  const edges = generations[depth], panel = panels[depth];
  const ids = [...new Set(edges.flatMap(edge => [edge.tail, edge.head]))];
  tex.push(`% Xi^${depth}: ${edges.length} edges; ${ids.length} ambient vertices.`);
  for (const id of ids) {
    const v = vertices[id];
    tex.push(`\\coordinate (r${depth}v${id}) at (${f(panel.centre + panel.width*v.x)},${f(panel.width*v.y)});`);
  }
  // Edge colours encode the mathematical state; labels are black.
  for (const edge of edges) tex.push(`\\draw[sampleedge,${colours[edge.colour]}] (r${depth}v${edge.tail}) -- (r${depth}v${edge.head});`);
  for (const id of ids) tex.push(`\\node[samplevertex] at (r${depth}v${id}) {};`);
  tex.push(`\\node[text=black,below=4pt] at (r${depth}v0) {$\\mathfrak v_+$};`);
  tex.push(`\\node[text=black,below=4pt] at (r${depth}v1) {$\\mathfrak v_-$};`);
  tex.push(`\\node[text=black] at (${panel.centre},-1.86) {$\\Xi_1^{${depth}}$};`);
}
for (const [x1, x2] of [[1.65,1.95],[4.55,5.05],[8.95,9.5]])
  tex.push(`\\draw[->,black!55,line width=.7pt] (${x1},0) -- (${x2},0);`);
tex.push('\\node[text=black] at (15.4,0) {$\\cdots$};', '\\end{tikzpicture}', '');
fs.writeFileSync(output, tex.join('\n'));
const audit = {seed, prng: 'Mulberry32', p, sampling: 'Independent Bernoulli indicators conditioned by rejection; cemetery indicators unrevealed',
  output: 'figure/random_DHL-realisation-corrected.tex', dimensionsCm: {width: 15.6, height: 3.7}, checks, transitions,
  vertices, generations, passed: true};
fs.writeFileSync(auditOutput, JSON.stringify(audit, null, 2) + '\n');
console.log(JSON.stringify({output, auditOutput, checks}, null, 2));
