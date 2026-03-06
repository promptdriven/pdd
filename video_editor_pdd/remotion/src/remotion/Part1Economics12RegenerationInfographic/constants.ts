// Part1Economics12RegenerationInfographic constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0A1628";
export const FPS = 30;
export const TOTAL_FRAMES = 750;

// Colors
export const BLUE = "#3B82F6";
export const GREEN = "#22C55E";
export const AMBER = "#F59E0B";
export const MUTED = "#94A3B8";
export const AXIS_COLOR = "#94A3B8";
export const AXIS_TITLE_COLOR = "#CBD5E1";
export const GRID_COLOR = "#334155";
export const WHITE = "#FFFFFF";
export const DANGER_RED = "#EF4444";

// Part A — Compression Ratio layout
export const SMALL_DOC_POS = { x: 300, y: 260 };
export const SMALL_DOC_SIZE = { w: 80, h: 100 };
export const LARGE_DOC_POS = { x: 1400, y: 200 };
export const LARGE_DOC_SIZE = { w: 200, h: 220 };
export const ARROW_FROM = { x: 420, y: 260 };
export const ARROW_TO = { x: 1300, y: 260 };
export const ARROW_START_WIDTH = 4;
export const ARROW_END_WIDTH = 24;

// Part B — U-Curve layout
export const CHART_LEFT = 380;
export const CHART_TOP = 520;
export const CHART_WIDTH = 1160;
export const CHART_HEIGHT = 380;

// U-curve data points
export const U_CURVE_POINTS = [
  { x: 10, y: 0.85 },
  { x: 50, y: 0.55 },
  { x: 100, y: 0.3 },
  { x: 200, y: 0.12 },
  { x: 250, y: 0.08 },
  { x: 300, y: 0.1 },
  { x: 500, y: 0.35 },
  { x: 750, y: 0.6 },
  { x: 1000, y: 0.82 },
];

export const SWEET_SPOT_X = 250;
export const SWEET_SPOT_Y = 0.08;
export const X_MAX = 1050;
export const Y_MAX = 1.0;

// X-axis and Y-axis ticks
export const X_TICKS = [0, 250, 500, 750, 1000];
export const Y_TICKS = [0, 0.25, 0.5, 0.75, 1.0];

// Animation frames (at 30fps)
export const SMALL_DOC_START = 0;
export const SMALL_DOC_END = 30;
export const ARROW_DRAW_START = 20;
export const ARROW_DRAW_END = 60;
export const LARGE_DOC_START = 50;
export const LARGE_DOC_END = 80;
export const LABELS_START = 70;
export const LABELS_END = 90;
export const AXES_FADE_START = 100;
export const AXES_FADE_END = 130;
export const CURVE_DRAW_START = 130;
export const CURVE_DRAW_END = 200;
export const SWEET_SPOT_START = 190;
export const BADGE_START = 210;
export const BADGE_END = 240;

// Approximate SVG path length for dash animation
export const CURVE_PATH_LENGTH = 2000;
