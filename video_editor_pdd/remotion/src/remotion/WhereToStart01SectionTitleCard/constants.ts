// constants.ts — WhereToStart01SectionTitleCard

export const CANVAS = {
  WIDTH: 1920,
  HEIGHT: 1080,
  BG: '#0A0F1A',
} as const;

export const GRID = {
  SPACING: 60,
  COLOR: '#1E293B',
  OPACITY: 0.05,
} as const;

export const COLORS = {
  TITLE: '#E2E8F0',
  LABEL: '#64748B',
  RULE: '#334155',
  NODE: '#94A3B8',
  HIGHLIGHT: '#4A90D9',
} as const;

export const TITLE = {
  LINE1: 'WHERE TO',
  LINE2: 'START',
  LABEL: 'WHERE TO START',
  FONT_SIZE: 72,
  FONT_WEIGHT: 700,
  LABEL_SIZE: 14,
  LABEL_WEIGHT: 600,
  LABEL_LETTER_SPACING: 4,
  LINE1_Y: 460,
  LINE2_Y: 545,
  LINE2_OFFSET_X: 15,
  LABEL_Y: 400,
  RULE_Y: 505,
  RULE_WIDTH: 200,
  RULE_HEIGHT: 2,
} as const;

export const TOPOLOGY = {
  NODE_COUNT: 35,
  NODE_RADIUS: 6,
  NODE_OPACITY: 0.03,
  EDGE_OPACITY: 0.015,
  AREA_WIDTH: 800,
  AREA_HEIGHT: 500,
  HIGHLIGHT_INDEX: 28,
  HIGHLIGHT_X: 1200,
  HIGHLIGHT_Y: 600,
  HIGHLIGHT_OPACITY: 0.06,
  GLOW_BLUR: 12,
  GLOW_OPACITY: 0.03,
  PULSE_MIN: 0.04,
  PULSE_MAX: 0.08,
  PULSE_PERIOD: 40,
} as const;

export const TIMING = {
  BG_FADE_START: 0,
  BG_FADE_END: 15,
  TOPOLOGY_START: 15,
  TOPOLOGY_NODE_STAGGER: 1,
  TOPOLOGY_EDGE_DRAW: 30,
  LABEL_START: 15,
  LABEL_FADE: 20,
  TITLE_LINE1_START: 40,
  CHAR_DELAY: 3,
  RULE_START: 60,
  RULE_DRAW: 10,
  TITLE_LINE2_START: 70,
  TITLE_LINE2_FADE: 20,
  TITLE_LINE2_SLIDE: 10,
  TOTAL: 120,
} as const;

// Pre-generated node positions for the ghost topology (seeded pseudo-random)
// Spread across 800x500 centered at (960, 540)
function generateNodes(count: number): Array<{ x: number; y: number }> {
  const cx = 960;
  const cy = 540;
  const w = 800;
  const h = 500;
  const nodes: Array<{ x: number; y: number }> = [];
  // Use a simple seeded approach for deterministic positions
  let seed = 42;
  const next = () => {
    seed = (seed * 16807 + 0) % 2147483647;
    return (seed - 1) / 2147483646;
  };
  for (let i = 0; i < count; i++) {
    const x = cx - w / 2 + next() * w;
    const y = cy - h / 2 + next() * h;
    nodes.push({ x: Math.round(x), y: Math.round(y) });
  }
  // Override highlight node position
  if (count > TOPOLOGY.HIGHLIGHT_INDEX) {
    nodes[TOPOLOGY.HIGHLIGHT_INDEX] = { x: TOPOLOGY.HIGHLIGHT_X, y: TOPOLOGY.HIGHLIGHT_Y };
  }
  return nodes;
}

function generateEdges(
  nodes: Array<{ x: number; y: number }>,
): Array<[number, number]> {
  const edges: Array<[number, number]> = [];
  // Connect each node to 1-3 nearby nodes
  for (let i = 0; i < nodes.length; i++) {
    const distances = nodes
      .map((n, j) => ({
        j,
        d: Math.hypot(n.x - nodes[i].x, n.y - nodes[i].y),
      }))
      .filter((e) => e.j !== i)
      .sort((a, b) => a.d - b.d);
    const connectCount = 1 + (i % 3);
    for (let c = 0; c < connectCount && c < distances.length; c++) {
      const j = distances[c].j;
      // Avoid duplicate edges
      if (!edges.some(([a, b]) => (a === i && b === j) || (a === j && b === i))) {
        edges.push([i, j]);
      }
    }
  }
  return edges;
}

export const NODES = generateNodes(TOPOLOGY.NODE_COUNT);
export const EDGES = generateEdges(NODES);
