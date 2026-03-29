// === Colors ===
export const BG_COLOR = "#0A0F1A";
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.06;
export const AXIS_COLOR = "#334155";
export const LABEL_COLOR = "#94A3B8";
export const CURVE_COLOR = "#E2E8F0";
export const DOT_COLOR = "#FFFFFF";
export const AMBER_ZONE = "#D9944A";
export const BLUE_ZONE = "#4A90D9";

// === Dimensions ===
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const GRID_SPACING = 160;

// === Chart Area ===
export const CHART_LEFT = 200;
export const CHART_TOP = 120;
export const CHART_RIGHT = 1720;
export const CHART_BOTTOM = 880;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT; // 1520
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP; // 760

// === Data ===
export const CURVE_DATA: { x: number; y: number }[] = [
  { x: 0, y: 0.95 },
  { x: 5, y: 0.70 },
  { x: 10, y: 0.45 },
  { x: 15, y: 0.32 },
  { x: 20, y: 0.25 },
  { x: 30, y: 0.18 },
  { x: 40, y: 0.14 },
  { x: 50, y: 0.12 },
];

export const X_MIN = 0;
export const X_MAX = 50;
export const Y_MIN = 0;
export const Y_MAX = 1;

// === Timing (frames) ===
export const AXES_START = 0;
export const AXES_DURATION = 45;
export const CURVE_START = 45;
export const CURVE_DURATION = 135;
export const DOT_APPEAR_FRAME = 180;
export const LEFT_CALLOUT_START = 180;
export const DOT_TRAVERSE_START = 240;
export const DOT_TRAVERSE_DURATION = 210;
export const RIGHT_CALLOUT_START = 450;
export const FADEOUT_START = 630;
export const FADEOUT_DURATION = 60;
export const TOTAL_FRAMES = 690;

// === Typography ===
export const FONT_FAMILY = "Inter, sans-serif";
export const AXIS_TICK_FONT_SIZE = 14;
export const AXIS_TITLE_FONT_SIZE = 16;
export const CALLOUT_FONT_SIZE = 14;

// === Dot ===
export const DOT_RADIUS = 10;
export const GLOW_RADIUS = 16;
export const GLOW_OPACITY = 0.2;

// === Zone shading ===
export const ZONE_OPACITY = 0.06;
export const ZONE_TRANSITION_X = 20;

// === X-axis tick values ===
export const X_TICKS = [0, 10, 20, 30, 40, 50];
