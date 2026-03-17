// ─── Colors ───
export const BG_COLOR = '#0A1225';
export const RADIAL_GLOW_COLOR = '#1E293B';
export const RADIAL_GLOW_OPACITY = 0.04;

export const EDGE_COLOR = '#475569';
export const EDGE_OPACITY = 0.6;
export const EDGE_GLOW_BLUR = 4;
export const EDGE_GLOW_OPACITY = 0.06;

export const NODE_BLUE = '#4A90D9';
export const NODE_ORANGE = '#D9944A';
export const NODE_GREEN = '#5AAA6E';

export const CODE_LINE_COLOR = '#94A3B8';
export const CODE_LINE_OPACITY = 0.15;

export const TERMINAL_COLOR = '#4A90D9';
export const TERMINAL_OPACITY = 0.2;

// ─── Geometry ───
export const CENTER_X = 960;
export const CENTER_Y = 520;
export const TRIANGLE_SIDE = 500;

export const VERTICES: [number, number][] = [
  [960, 280],  // top
  [710, 713],  // bottom-left
  [1210, 713], // bottom-right
];

export const NODE_RADIUS = 20;
export const NODE_PULSE_MIN = 20;
export const NODE_PULSE_MAX = 22;
export const NODE_PULSE_PERIOD = 60;

// ─── Labels ───
export const NODE_LABELS: { text: string; pos: [number, number]; color: string }[] = [
  { text: 'Prompt', pos: [960, 250], color: NODE_BLUE },
  { text: 'Diff', pos: [670, 743], color: NODE_ORANGE },
  { text: 'Drift', pos: [1250, 743], color: NODE_GREEN },
];

// ─── Code Patterns (different line sets for each cycle) ───
export interface CodeLineData {
  width: number;
  offsetX: number;
  offsetY: number;
}

export const CODE_PATTERN_1: CodeLineData[] = [
  { width: 160, offsetX: -40, offsetY: -35 },
  { width: 120, offsetX: 10, offsetY: -25 },
  { width: 180, offsetX: -20, offsetY: -15 },
  { width: 80, offsetX: 30, offsetY: -5 },
  { width: 140, offsetX: -10, offsetY: 5 },
  { width: 100, offsetX: 20, offsetY: 15 },
  { width: 170, offsetX: -30, offsetY: 25 },
  { width: 60, offsetX: 40, offsetY: 35 },
];

export const CODE_PATTERN_2: CodeLineData[] = [
  { width: 100, offsetX: 20, offsetY: -40 },
  { width: 150, offsetX: -30, offsetY: -28 },
  { width: 70, offsetX: 45, offsetY: -16 },
  { width: 180, offsetX: -10, offsetY: -4 },
  { width: 90, offsetX: 35, offsetY: 8 },
  { width: 130, offsetX: -25, offsetY: 20 },
  { width: 160, offsetX: 5, offsetY: 32 },
  { width: 110, offsetX: -15, offsetY: 44 },
  { width: 60, offsetX: 50, offsetY: 56 },
];

export const CODE_PATTERN_3: CodeLineData[] = [
  { width: 140, offsetX: -15, offsetY: -30 },
  { width: 80, offsetX: 40, offsetY: -20 },
  { width: 170, offsetX: -35, offsetY: -10 },
  { width: 110, offsetX: 15, offsetY: 0 },
  { width: 60, offsetX: -45, offsetY: 10 },
  { width: 150, offsetX: 25, offsetY: 20 },
  { width: 90, offsetX: -5, offsetY: 30 },
];

export const CODE_PATTERN_4: CodeLineData[] = [
  { width: 120, offsetX: 10, offsetY: -38 },
  { width: 170, offsetX: -25, offsetY: -26 },
  { width: 60, offsetX: 35, offsetY: -14 },
  { width: 140, offsetX: -40, offsetY: -2 },
  { width: 100, offsetX: 20, offsetY: 10 },
  { width: 80, offsetX: -10, offsetY: 22 },
  { width: 160, offsetX: 5, offsetY: 34 },
  { width: 130, offsetX: -20, offsetY: 46 },
];

// ─── Cycle Timing ───
export interface CycleConfig {
  startFrame: number;
  dissolveFrames: number;
  regenerateFrames: number;
  particlesPerLine: number;
  driftRadius: number;
  fadeDuration: number;
  staggerFrames: number;
  sourcePattern: CodeLineData[];
  targetPattern: CodeLineData[];
}

export const CYCLES: CycleConfig[] = [
  {
    startFrame: 10,
    dissolveFrames: 30,
    regenerateFrames: 30,
    particlesPerLine: 6,
    driftRadius: 120,
    fadeDuration: 15,
    staggerFrames: 6,
    sourcePattern: CODE_PATTERN_1,
    targetPattern: CODE_PATTERN_2,
  },
  {
    startFrame: 70,
    dissolveFrames: 25,
    regenerateFrames: 25,
    particlesPerLine: 5,
    driftRadius: 100,
    fadeDuration: 12,
    staggerFrames: 4,
    sourcePattern: CODE_PATTERN_2,
    targetPattern: CODE_PATTERN_3,
  },
  {
    startFrame: 120,
    dissolveFrames: 20,
    regenerateFrames: 20,
    particlesPerLine: 4,
    driftRadius: 80,
    fadeDuration: 10,
    staggerFrames: 2,
    sourcePattern: CODE_PATTERN_3,
    targetPattern: CODE_PATTERN_4,
  },
];

// ─── Terminal ───
export const TERMINAL_X = 1640;
export const TERMINAL_Y = 980;
export const TERMINAL_FONT_SIZE = 10;

// Terminal cycle times: when each "✓" appears
export const TERMINAL_CHECK_FRAMES = [40, 95, 140];
