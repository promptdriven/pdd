// ─── Colors ────────────────────────────────────────────────────────────────
export const BG_COLOR = '#0D1117';
export const AXIS_COLOR = '#334155';
export const GRID_COLOR = '#334155';
export const LABEL_COLOR = '#94A3B8';
export const CROSSING_LABEL_COLOR = '#E2E8F0';
export const AMBER = '#D9944A';
export const BLUE = '#4A90D9';

// ─── Opacities ─────────────────────────────────────────────────────────────
export const AXIS_OPACITY = 0.25;
export const GRID_OPACITY = 0.08;
export const LABEL_OPACITY = 0.3;
export const TICK_LABEL_OPACITY = 0.25;
export const LINE_LABEL_OPACITY = 0.7;
export const CROSSING_LABEL_OPACITY = 0.85;
export const ANNOTATION_OPACITY = 0.3;
export const SHADED_AREA_OPACITY = 0.06;

// ─── Layout (px) ───────────────────────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const MARGIN_LEFT = 280;
export const MARGIN_RIGHT = 160;
export const MARGIN_TOP = 140;
export const MARGIN_BOTTOM = 120;
export const CHART_WIDTH = WIDTH - MARGIN_LEFT - MARGIN_RIGHT;   // 1480
export const CHART_HEIGHT = HEIGHT - MARGIN_TOP - MARGIN_BOTTOM; // 820

// ─── Axis ranges ───────────────────────────────────────────────────────────
export const X_MIN = 1950;
export const X_MAX = 1975;
export const Y_MIN = 0;
export const Y_MAX = 100;

// ─── Data series ───────────────────────────────────────────────────────────
export interface DataPoint {
  x: number;
  y: number;
}

export const LABOR_COST_DATA: DataPoint[] = [
  { x: 1950, y: 35 },
  { x: 1955, y: 34 },
  { x: 1960, y: 33 },
  { x: 1965, y: 33 },
  { x: 1970, y: 32 },
  { x: 1975, y: 32 },
];

export const SOCK_COST_DATA: DataPoint[] = [
  { x: 1950, y: 80 },
  { x: 1955, y: 55 },
  { x: 1960, y: 38 },
  { x: 1962, y: 33 },
  { x: 1965, y: 25 },
  { x: 1970, y: 18 },
  { x: 1975, y: 14 },
];

export const CROSSING_POINT: DataPoint = { x: 1962, y: 33 };

// ─── Timing (frames @ 30fps) ──────────────────────────────────────────────
export const FPS = 30;
export const TOTAL_FRAMES = 540;

export const AXES_START = 0;
export const AXES_DURATION = 30;

export const LINES_START = 30;
export const LINES_DRAW_DURATION = 270; // lines finish at frame 300

export const CROSSING_APPEAR_FRAME = 150;
export const CROSSING_FADE_DURATION = 15;

export const SHADING_START = 180;
export const SHADING_FADE_DURATION = 20;

export const IRRATIONAL_LABEL_START = 300;
export const IRRATIONAL_LABEL_FADE = 15;

// ─── Typography ────────────────────────────────────────────────────────────
export const FONT_FAMILY = 'Inter, system-ui, -apple-system, sans-serif';
