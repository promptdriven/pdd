// constants.ts — PDD Triangle visual constants

export const CANVAS = {
  width: 1920,
  height: 1080,
  background: '#0A0F1A',
} as const;

export const GLOW = {
  centerX: 960,
  centerY: 520,
  radius: 600,
  color: '#1E293B',
  opacity: 0.04,
} as const;

export const TRIANGLE = {
  sideLength: 500,
  edgeColor: '#334155',
  edgeOpacity: 0.4,
  edgeWidth: 2,
  glowBlur: 4,
  glowOpacity: 0.15,
} as const;

export const NODES = {
  prompt: {
    id: 'prompt',
    label: 'PROMPT',
    descriptor: 'encode intent',
    cx: 960,
    cy: 200,
    color: '#60A5FA',
    labelY: 160,
    descriptorY: 185,
    labelBelow: false,
  },
  tests: {
    id: 'tests',
    label: 'TESTS',
    descriptor: 'preserve behavior',
    cx: 480,
    cy: 750,
    color: '#4ADE80',
    labelY: 800,
    descriptorY: 825,
    labelBelow: true,
  },
  grounding: {
    id: 'grounding',
    label: 'GROUNDING',
    descriptor: 'maintain style',
    cx: 1440,
    cy: 750,
    color: '#D9944A',
    labelY: 800,
    descriptorY: 825,
    labelBelow: true,
  },
} as const;

export const NODE_RADIUS = 20;
export const NODE_PULSE_MIN = 20;
export const NODE_PULSE_MAX = 22;
export const NODE_PULSE_PERIOD = 60;

export const EDGES = [
  { from: [960, 200] as const, to: [480, 750] as const, startFrame: 30 },
  { from: [480, 750] as const, to: [1440, 750] as const, startFrame: 60 },
  { from: [1440, 750] as const, to: [960, 200] as const, startFrame: 90 },
] as const;

// Animation timing
export const TIMING = {
  bgFadeIn: { start: 0, duration: 30 },
  promptNode: { start: 30, circleDuration: 15, labelDuration: 12 },
  testsNode: { start: 60, circleDuration: 15, labelDuration: 12 },
  groundingNode: { start: 90, circleDuration: 15, labelDuration: 12 },
  descriptorPrompt: { start: 120, duration: 15 },
  descriptorTests: { start: 135, duration: 15 },
  descriptorGrounding: { start: 150, duration: 15 },
  codeLines: { start: 170, fadeDuration: 8, stagger: 4 },
  pulseStart: 230,
  edgeDrawDuration: 25,
} as const;

// Code lines config
export const CODE_LINES_CONFIG = {
  centerX: 960,
  centerY: 520,
  count: 9,
  color: '#94A3B8',
  opacity: 0.15,
  lineHeight: 8,
  gap: 4,
  widths: [140, 100, 170, 80, 150, 120, 60, 180, 110],
} as const;
