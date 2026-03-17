// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0D1117";
export const FPS = 30;
export const TOTAL_FRAMES = 540;

// Chart area margins
export const MARGIN_LEFT = 280;
export const MARGIN_RIGHT = 100;
export const MARGIN_TOP = 140;
export const MARGIN_BOTTOM = 120;

// Derived chart dimensions
export const CHART_WIDTH = WIDTH - MARGIN_LEFT - MARGIN_RIGHT;
export const CHART_HEIGHT = HEIGHT - MARGIN_TOP - MARGIN_BOTTOM;

// Axis ranges
export const X_MIN = 1950;
export const X_MAX = 1975;
export const Y_MIN = 0;
export const Y_MAX = 100;
export const X_MAJOR_INTERVAL = 5;
export const X_MINOR_INTERVAL = 1;
export const Y_MAJOR_INTERVAL = 25;

// Colors
export const AXIS_COLOR = "#334155";
export const AXIS_OPACITY = 0.25;
export const GRID_COLOR = "#334155";
export const GRID_OPACITY = 0.08;
export const LABEL_COLOR = "#94A3B8";
export const AMBER = "#D9944A";
export const BLUE = "#4A90D9";
export const CROSSING_LABEL_COLOR = "#E2E8F0";
export const CROSSING_GLOW_COLOR = "#FFFFFF";

// Typography
export const AXIS_LABEL_SIZE = 12;
export const TICK_LABEL_SIZE = 10;
export const LINE_LABEL_SIZE = 12;
export const CROSSING_LABEL_SIZE = 18;
export const ANNOTATION_LABEL_SIZE = 11;

// Line styling
export const LINE_STROKE_WIDTH = 3;

// Data series — Labor Cost to Darn (roughly flat ~33-35%)
export const LABOR_COST_DATA: { x: number; y: number }[] = [
  { x: 1950, y: 35 },
  { x: 1955, y: 34 },
  { x: 1960, y: 33 },
  { x: 1962, y: 33 },
  { x: 1965, y: 33 },
  { x: 1970, y: 32 },
  { x: 1975, y: 32 },
];

// Data series — New Sock Cost (declining from 80% to 14%)
export const SOCK_COST_DATA: { x: number; y: number }[] = [
  { x: 1950, y: 80 },
  { x: 1955, y: 55 },
  { x: 1960, y: 38 },
  { x: 1962, y: 33 },
  { x: 1965, y: 25 },
  { x: 1970, y: 18 },
  { x: 1975, y: 14 },
];

// Crossing point
export const CROSSING_X = 1962;
export const CROSSING_Y = 33;
export const CROSSING_DOT_RADIUS = 8;
export const CROSSING_GLOW_RADIUS = 16;

// Animation timing (frames)
export const AXES_DRAW_START = 0;
export const AXES_DRAW_END = 30;
export const GRID_FADE_START = 10;
export const GRID_FADE_END = 30;

export const LINES_DRAW_START = 30;
export const LINES_DRAW_END = 300;

export const CROSSING_APPEAR_START = 150;
export const CROSSING_LABEL_FADE_START = 155;
export const CROSSING_LABEL_FADE_END = 170;

export const SHADED_AREA_START = 180;
export const SHADED_AREA_END = 200;

export const ANNOTATION_FADE_START = 300;
export const ANNOTATION_FADE_END = 315;

export const LINE_LABELS_FADE_START = 305;
export const LINE_LABELS_FADE_END = 320;
