// Part4Precision03PrecisionCostUcurve constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0A1628";

// Chart region
export const CHART_LEFT = 200;
export const CHART_RIGHT = 1820;
export const CHART_TOP = 80;
export const CHART_BOTTOM = 880;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// Colors
export const CURVE_COLOR = "#3B82F6";
export const AMBER = "#F59E0B";
export const RED = "#EF4444";
export const AXIS_COLOR = "#94A3B8";
export const AXIS_TITLE_COLOR = "#CBD5E1";
export const GRID_COLOR = "#334155";
export const SWEET_SPOT_SUBLABEL_COLOR = "#CBD5E1";

// U-curve data points (normalized 0-1)
export const U_CURVE_POINTS = [
  { x: 0.0, y: 0.85 },
  { x: 0.1, y: 0.65 },
  { x: 0.2, y: 0.45 },
  { x: 0.3, y: 0.30 },
  { x: 0.4, y: 0.20 },
  { x: 0.5, y: 0.15 },
  { x: 0.6, y: 0.18 },
  { x: 0.7, y: 0.28 },
  { x: 0.8, y: 0.45 },
  { x: 0.9, y: 0.68 },
  { x: 1.0, y: 0.90 },
];

export const SWEET_SPOT = { x: 0.5, y: 0.15 };

// Danger zones (normalized x ranges)
export const LEFT_DANGER = { xStart: 0.0, xEnd: 0.185 };
export const RIGHT_DANGER = { xStart: 0.815, xEnd: 1.0 };

// Animation timing (frames at 30fps)
export const AXES_FADE_START = 0;
export const AXES_FADE_END = 30;

export const GRID_FADE_START = 20;
export const GRID_FADE_END = 50;

export const LEFT_DANGER_FADE_START = 40;
export const LEFT_DANGER_FADE_END = 70;

export const RIGHT_DANGER_FADE_START = 60;
export const RIGHT_DANGER_FADE_END = 90;

export const CURVE_DRAW_START = 70;
export const CURVE_DRAW_END = 220;

export const SWEET_DOT_START = 200;
export const SWEET_DOT_END = 240;

export const SWEET_LABEL_START = 230;
export const SWEET_LABEL_END = 260;

export const CHART_FADE_OUT_START = 850;
export const CHART_FADE_OUT_END = 900;

export const TOTAL_FRAMES = 900;
export const FPS = 30;

// Typography
export const FONT_FAMILY = "Inter, sans-serif";
