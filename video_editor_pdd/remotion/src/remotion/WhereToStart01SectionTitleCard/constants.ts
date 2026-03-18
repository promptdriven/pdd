// constants.ts — WhereToStart01SectionTitleCard

export const CANVAS = {
  width: 1920,
  height: 1080,
  backgroundColor: '#0A0F1A',
} as const;

export const GRID = {
  spacing: 60,
  color: '#1E293B',
  opacity: 0.05,
} as const;

export const COLORS = {
  textPrimary: '#E2E8F0',
  textSecondary: '#64748B',
  rule: '#334155',
  nodeColor: '#94A3B8',
  highlightNode: '#4A90D9',
} as const;

export const TITLE = {
  line1: 'WHERE TO',
  line2: 'START',
  sectionLabel: 'WHERE TO START',
  fontSize: 72,
  fontWeight: 700 as const,
  labelFontSize: 14,
  labelFontWeight: 600 as const,
  labelLetterSpacing: 4,
  line1Y: 460,
  line2Y: 545,
  line2OffsetX: 15,
  ruleY: 505,
  ruleWidth: 200,
  ruleHeight: 2,
  labelY: 400,
} as const;

// Topology node positions — 35 nodes spread across ~800×500 centered area
// Center of canvas: (960, 540), so from roughly (560, 290) to (1360, 790)
export const TOPOLOGY_NODES: Array<{ x: number; y: number }> = [
  { x: 620, y: 340 }, { x: 700, y: 310 }, { x: 780, y: 350 },
  { x: 660, y: 420 }, { x: 740, y: 400 }, { x: 820, y: 380 },
  { x: 900, y: 320 }, { x: 980, y: 340 }, { x: 1060, y: 310 },
  { x: 1140, y: 350 }, { x: 600, y: 500 }, { x: 680, y: 480 },
  { x: 760, y: 520 }, { x: 840, y: 460 }, { x: 920, y: 500 },
  { x: 1000, y: 470 }, { x: 1080, y: 490 }, { x: 1160, y: 460 },
  { x: 1240, y: 500 }, { x: 640, y: 580 }, { x: 720, y: 620 },
  { x: 800, y: 590 }, { x: 880, y: 630 }, { x: 960, y: 600 },
  { x: 1040, y: 580 }, { x: 1120, y: 620 }, { x: 1200, y: 600 },
  { x: 1280, y: 580 }, { x: 700, y: 700 }, { x: 800, y: 720 },
  { x: 900, y: 690 }, { x: 1000, y: 710 }, { x: 1100, y: 700 },
  { x: 1200, y: 730 }, { x: 1300, y: 690 },
];

// Index of the highlighted/glowing node (at edge position ~1200, 600)
export const HIGHLIGHT_NODE_INDEX = 26;

// Edges connecting nodes (index pairs)
export const TOPOLOGY_EDGES: Array<[number, number]> = [
  [0, 1], [1, 2], [0, 3], [1, 4], [2, 5],
  [3, 4], [4, 5], [5, 6], [6, 7], [7, 8],
  [8, 9], [3, 10], [3, 11], [4, 13], [5, 13],
  [10, 11], [11, 12], [12, 13], [13, 14], [14, 15],
  [15, 16], [16, 17], [17, 18], [6, 14], [7, 15],
  [8, 16], [9, 17], [10, 19], [11, 20], [12, 21],
  [13, 22], [14, 23], [15, 24], [16, 25], [17, 26],
  [18, 27], [19, 20], [20, 21], [21, 22], [22, 23],
  [23, 24], [24, 25], [25, 26], [26, 27], [19, 28],
  [20, 29], [21, 30], [22, 31], [23, 32], [24, 33],
  [25, 34], [28, 29], [29, 30], [30, 31], [31, 32],
  [32, 33], [33, 34],
];

// Animation timing (frames)
export const TIMING = {
  bgFadeIn: { start: 0, end: 15 },
  labelFadeIn: { start: 15, duration: 20 },
  topologyDraw: { start: 15, nodeStagger: 1, edgeDrawDuration: 30 },
  line1TypeOn: { start: 40, charDelay: 3 },
  ruleDraw: { start: 60, duration: 10 },
  line2FadeSlide: { start: 70, duration: 20 },
  nodePulsePeriod: 40,
} as const;

export const OPACITIES = {
  labelText: 0.5,
  rule: 0.5,
  nodeBase: 0.03,
  edgeBase: 0.015,
  highlightNode: 0.06,
  highlightGlow: 0.03,
  highlightPulseMin: 0.04,
  highlightPulseMax: 0.08,
} as const;
