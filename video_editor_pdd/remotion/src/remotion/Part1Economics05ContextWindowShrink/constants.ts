// === Colors ===
export const BG_COLOR = '#0D1117';
export const BLOCK_FILL = '#1A2332';
export const BLOCK_BORDER = '#334155';
export const CONTEXT_WINDOW_COLOR = '#4A90D9';
export const TEXT_MUTED = '#94A3B8';
export const TEXT_LIGHT = '#E2E8F0';

export const COLOR_GREEN = '#5AAA6E';
export const COLOR_YELLOW = '#D9C44A';
export const COLOR_AMBER = '#D9944A';
export const COLOR_RED = '#E74C3C';

// === Dimensions ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const GRID_AREA_SIZE = 800;
export const GRID_CENTER_X = 560; // left-center area
export const GRID_CENTER_Y = 540; // vertical center
export const CONTEXT_WINDOW_SIZE = 480;

export const INSET_X = 1540;
export const INSET_Y = 820;
export const INSET_WIDTH = 320;
export const INSET_HEIGHT = 200;

export const COUNTER_X = 1580;
export const COUNTER_Y = 100;

// === Grid Stages ===
export interface GridStage {
  gridSize: number;
  coverage: number;
  coverageColor: string;
  startFrame: number; // relative to grid sequence start (frame 30)
}

export const GRID_STAGES: GridStage[] = [
  { gridSize: 4, coverage: 80, coverageColor: COLOR_GREEN, startFrame: 0 },
  { gridSize: 8, coverage: 40, coverageColor: COLOR_YELLOW, startFrame: 60 },
  { gridSize: 16, coverage: 10, coverageColor: COLOR_AMBER, startFrame: 150 },
  { gridSize: 32, coverage: 2, coverageColor: COLOR_RED, startFrame: 240 },
];

export const MORPH_DURATION = 40;
export const GAP = 8;

// === Animation Timing (absolute frames) ===
export const GRID_START = 30;
export const HIGHLIGHTS_START = 360;
export const INSET_START = 480;
export const HOLD_START = 600;
export const TOTAL_FRAMES = 900;

// === Highlight positions (relative cell indices in 32x32 grid) ===
// Red highlights: inside the context window but irrelevant
export const RED_HIGHLIGHTS = [
  { row: 12, col: 13 },
  { row: 14, col: 12 },
  { row: 13, col: 15 },
  { row: 15, col: 14 },
];

// Green highlights: outside the context window but needed
export const GREEN_HIGHLIGHTS = [
  { row: 2, col: 3 },
  { row: 5, col: 28 },
  { row: 24, col: 7 },
  { row: 28, col: 25 },
  { row: 8, col: 30 },
  { row: 30, col: 15 },
];

// === Performance graph data points ===
export const PERF_DATA = [
  { x: 0, y: 95 },
  { x: 0.15, y: 90 },
  { x: 0.3, y: 82 },
  { x: 0.45, y: 70 },
  { x: 0.6, y: 55 },
  { x: 0.75, y: 38 },
  { x: 0.9, y: 22 },
  { x: 1.0, y: 12 },
];

// Faux code lines for blocks
export const FAUX_CODE_LINES = [
  'fn init() {',
  '  let x = 0;',
  '  return x;',
  '}',
];
