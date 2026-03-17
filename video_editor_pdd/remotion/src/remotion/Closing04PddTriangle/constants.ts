// constants.ts — PDD Triangle colors, dimensions, and node data

export const CANVAS = {
  WIDTH: 1920,
  HEIGHT: 1080,
  BG_COLOR: '#0A1225',
  GLOW_COLOR: '#1E293B',
  GLOW_OPACITY: 0.04,
  GLOW_RADIUS: 600,
  CENTER: { x: 960, y: 520 },
} as const;

export const TRIANGLE = {
  SIDE_LENGTH: 500,
  EDGE_COLOR: '#475569',
  EDGE_OPACITY: 0.6,
  EDGE_WIDTH: 2,
  EDGE_GLOW_BLUR: 4,
  EDGE_GLOW_OPACITY: 0.06,
} as const;

export const NODES = {
  PROMPT: {
    id: 'prompt',
    label: 'PROMPT',
    descriptor: 'Encodes intent',
    color: '#4A90D9',
    cx: 960,
    cy: 280,
    labelY: 248,
    descriptorY: 232,
    labelAnchor: 'above' as const,
  },
  TESTS: {
    id: 'tests',
    label: 'TESTS',
    descriptor: 'Preserve behavior',
    color: '#D9944A',
    cx: 710,
    cy: 713,
    labelY: 748,
    descriptorY: 768,
    labelAnchor: 'below' as const,
  },
  GROUNDING: {
    id: 'grounding',
    label: 'GROUNDING',
    descriptor: 'Maintains style',
    color: '#5AAA6E',
    cx: 1210,
    cy: 713,
    labelY: 748,
    descriptorY: 768,
    labelAnchor: 'below' as const,
  },
} as const;

export const NODE_RADIUS = 20;
export const NODE_PULSE_MIN = 20;
export const NODE_PULSE_MAX = 22;
export const NODE_PULSE_PERIOD = 60;

// Animation timing (frames)
export const TIMING = {
  // Phase 1: Background fade-in
  BG_START: 0,
  BG_END: 30,

  // Phase 2: PROMPT node + first edge
  PROMPT_NODE_START: 30,
  EDGE_1_START: 30,

  // Phase 3: TESTS node + second edge
  TESTS_NODE_START: 60,
  EDGE_2_START: 60,

  // Phase 4: GROUNDING node + third edge
  GROUNDING_NODE_START: 90,
  EDGE_3_START: 90,

  // Phase 5: Descriptors
  DESCRIPTOR_PROMPT_START: 120,
  DESCRIPTOR_TESTS_START: 135,
  DESCRIPTOR_GROUNDING_START: 150,

  // Phase 6: Code lines
  CODE_LINES_START: 170,

  // Phase 7: Pulse hold
  PULSE_START: 230,

  // Durations
  NODE_SCALE_DURATION: 15,
  EDGE_DRAW_DURATION: 25,
  LABEL_FADE_DURATION: 12,
  DESCRIPTOR_FADE_DURATION: 15,
  CODE_FADE_DURATION: 8,
  CODE_STAGGER: 4,

  TOTAL_FRAMES: 300,
} as const;

// Code lines configuration
export const CODE_LINES = {
  COUNT: 9,
  COLOR: '#94A3B8',
  OPACITY: 0.15,
  MIN_WIDTH: 60,
  MAX_WIDTH: 180,
  HEIGHT: 3,
  GAP: 10,
} as const;

// Pre-computed code line widths (deterministic for consistent renders)
export const CODE_LINE_WIDTHS = [120, 160, 80, 140, 100, 175, 65, 130, 95];
export const CODE_LINE_OFFSETS = [-2, 1, -1, 3, 0, -3, 2, -1, 1]; // slight x offsets
