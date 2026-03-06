// Part1Economics12RegenerationInfographic constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0A1628";

// Part A region — Compression Ratio (top half)
export const PART_A_LEFT = 200;
export const PART_A_RIGHT = 1720;
export const PART_A_TOP = 120;
export const PART_A_BOTTOM = 440;

// Part B region — U-Curve (bottom half)
export const CHART_LEFT = 300;
export const CHART_RIGHT = 1620;
export const CHART_TOP = 480;
export const CHART_BOTTOM = 920;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// Colors
export const BLUE = "#3B82F6";
export const GREEN = "#22C55E";
export const AMBER = "#F59E0B";
export const RED = "#EF4444";
export const WHITE = "#FFFFFF";
export const MUTED = "#94A3B8";
export const AXIS_COLOR = "#94A3B8";
export const AXIS_TITLE_COLOR = "#CBD5E1";
export const GRID_COLOR = "#334155";

// U-curve data points (x: module size 0-1000, y: defect rate 0-1)
export const U_CURVE_DATA = [
  { x: 10, y: 0.85 },
  { x: 50, y: 0.55 },
  { x: 100, y: 0.30 },
  { x: 200, y: 0.12 },
  { x: 250, y: 0.08 },
  { x: 300, y: 0.10 },
  { x: 500, y: 0.35 },
  { x: 750, y: 0.60 },
  { x: 1000, y: 0.82 },
];

// Normalized U-curve points (0-1 range for chart rendering)
export const U_CURVE_POINTS = U_CURVE_DATA.map((p) => ({
  x: p.x / 1000,
  y: p.y,
}));

export const SWEET_SPOT = { x: 250 / 1000, y: 0.08 };

// Doc icon positions
export const SMALL_DOC_POS = { x: 300, y: 260 };
export const SMALL_DOC_SIZE = { w: 80, h: 100 };
export const LARGE_DOC_POS = { x: 1400, y: 200 };
export const LARGE_DOC_SIZE = { w: 200, h: 220 };

// Arrow positions
export const ARROW_FROM = { x: 420, y: 260 };
export const ARROW_TO = { x: 1300, y: 260 };

// Animation timing (frames at 30fps)
// Part A — Compression Ratio
export const SMALL_DOC_FADE_START = 0;
export const SMALL_DOC_FADE_END = 30;

export const ARROW_DRAW_START = 20;
export const ARROW_DRAW_END = 60;

export const LARGE_DOC_FADE_START = 50;
export const LARGE_DOC_FADE_END = 80;

export const LABELS_FADE_START = 70;
export const LABELS_FADE_END = 90;

// Part B — U-Curve
export const AXES_FADE_START = 100;
export const AXES_FADE_END = 130;

export const CURVE_DRAW_START = 130;
export const CURVE_DRAW_END = 200;

export const SWEET_SPOT_START = 190;
export const SWEET_SPOT_END = 220;

export const BADGE_SLIDE_START = 210;
export const BADGE_SLIDE_END = 240;

// Hold until end
export const TOTAL_FRAMES = 750;
export const FPS = 30;

// Typography
export const FONT_FAMILY = "Inter, sans-serif";
