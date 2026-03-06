// Part1Economics03CostCrossoverChart constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0A1628";

// Chart area padding
export const PADDING_LEFT = 200;
export const PADDING_BOTTOM = 200;
export const PADDING_RIGHT = 100;
export const PADDING_TOP = 100;

// Derived chart region: (200, 100) to (1820, 880)
export const CHART_X = PADDING_LEFT;
export const CHART_Y = PADDING_TOP;
export const CHART_W = WIDTH - PADDING_LEFT - PADDING_RIGHT; // 1620
export const CHART_H = HEIGHT - PADDING_TOP - PADDING_BOTTOM; // 780

// Colors
export const PATCHING_COLOR_START = "#EF4444";
export const PATCHING_COLOR_END = "#F59E0B";
export const GENERATION_COLOR_START = "#3B82F6";
export const GENERATION_COLOR_END = "#22C55E";
export const TOTAL_COST_COLOR = "#94A3B8";
export const AXIS_COLOR = "#94A3B8";
export const AXIS_TITLE_COLOR = "#CBD5E1";
export const GRID_COLOR = "#334155";
export const CROSSOVER_DOT_COLOR = "#FFFFFF";
export const CROSSOVER_GLOW_COLOR = "#F59E0B";
export const LABEL_COLOR = "#FFFFFF";

// Line widths
export const PRIMARY_LINE_WIDTH = 4;
export const TOTAL_LINE_WIDTH = 2;

// Crossover point
export const CROSSOVER_DOT_RADIUS = 6;
export const CROSSOVER_GLOW_RADIUS = 30;

// Grid fractions for horizontal reference lines
export const GRID_FRACTIONS = [0.25, 0.5, 0.75];

// X-axis tick positions (normalized 0-1)
export const X_TICKS = [0, 0.2, 0.4, 0.6, 0.8, 1.0];

// Animation frames (at 30fps)
export const AXES_FADE_START = 0;
export const AXES_FADE_END = 30;
export const GRID_FADE_START = 30;
export const GRID_FADE_END = 90;
export const LINE_A_START = 60;
export const LINE_A_END = 180;
export const LINE_B_START = 120;
export const LINE_B_END = 240;
export const LINE_C_START = 200;
export const LINE_C_END = 260;
export const CROSSOVER_DOT_START = 250;
export const CROSSOVER_LABEL_START = 280;
export const CROSSOVER_LABEL_END = 310;
export const TOTAL_FRAMES = 2700;

// Act G zoom timing (relative to component start)
export const ZOOM_START = 2600;
export const ZOOM_END = 2700;

// Data points (normalized 0-1)
export const PATCHING_POINTS = [
  { x: 0, y: 0.15 },
  { x: 0.2, y: 0.22 },
  { x: 0.4, y: 0.35 },
  { x: 0.6, y: 0.55 },
  { x: 0.8, y: 0.78 },
  { x: 1.0, y: 0.95 },
];

export const GENERATION_POINTS = [
  { x: 0, y: 0.9 },
  { x: 0.2, y: 0.72 },
  { x: 0.4, y: 0.5 },
  { x: 0.6, y: 0.35 },
  { x: 0.8, y: 0.25 },
  { x: 1.0, y: 0.18 },
];

export const TOTAL_COST_POINTS = [
  { x: 0, y: 0.82 },
  { x: 0.2, y: 0.83 },
  { x: 0.4, y: 0.84 },
  { x: 0.6, y: 0.86 },
  { x: 0.8, y: 0.87 },
  { x: 1.0, y: 0.88 },
];

export const CROSSOVER_POINT = { x: 0.42, y: 0.48 };

// Derived crossover pixel position
export const CROSSOVER_PX_X = CHART_X + CROSSOVER_POINT.x * CHART_W;
export const CROSSOVER_PX_Y = CHART_Y + CHART_H * (1 - CROSSOVER_POINT.y);
