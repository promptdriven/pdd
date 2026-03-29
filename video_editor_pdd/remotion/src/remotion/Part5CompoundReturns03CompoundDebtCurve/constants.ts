// ── Colors ──────────────────────────────────────────────────────────
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.08;
export const AXIS_COLOR = '#334155';
export const AXIS_LABEL_COLOR = '#94A3B8';
export const AMBER_CURVE_COLOR = '#D9944A';
export const GREEN_LINE_COLOR = '#5AAA6E';
export const CALLOUT_TEXT_COLOR = '#E2E8F0';

// ── Dimensions ──────────────────────────────────────────────────────
export const CANVAS_W = 1920;
export const CANVAS_H = 1080;

// Chart area (padded from canvas edges)
export const CHART_LEFT = 160;
export const CHART_RIGHT = 1760;
export const CHART_TOP = 100;
export const CHART_BOTTOM = 920;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// Grid
export const GRID_SPACING = 150;

// ── Animation Frames ────────────────────────────────────────────────
export const TOTAL_FRAMES = 480;
export const AXES_SETTLE_END = 30;
export const CURVE_DRAW_START = 30;
export const CURVE_DRAW_END = 180;
export const CURVE_DRAW_DURATION = CURVE_DRAW_END - CURVE_DRAW_START; // 150
export const FORMULA_FADE_START = 90;
export const FORMULA_FADE_DURATION = 20;
export const GREEN_LINE_START = 180;
export const GREEN_LINE_END = 270;
export const GREEN_LINE_DURATION = GREEN_LINE_END - GREEN_LINE_START; // 90
export const ARROWS_START = 210;
export const ARROW_STAGGER = 10;
export const FLAT_LABEL_START = 270;
export const FLAT_LABEL_FADE_DURATION = 20;
export const CISQ_START = 330;
export const CISQ_FADE_DURATION = 25;

// ── Data ────────────────────────────────────────────────────────────
export interface DataPoint {
  x: number;
  y: number;
}

// Exponential debt curve — y values are normalized 0..1 (0 = bottom, 1 = top)
export const DEBT_EXPONENTIAL_DATA: DataPoint[] = [
  { x: 0, y: 0.05 },
  { x: 2, y: 0.07 },
  { x: 4, y: 0.10 },
  { x: 6, y: 0.14 },
  { x: 8, y: 0.20 },
  { x: 10, y: 0.30 },
  { x: 12, y: 0.42 },
  { x: 14, y: 0.58 },
  { x: 16, y: 0.72 },
  { x: 18, y: 0.85 },
  { x: 20, y: 0.95 },
];

// Flat regeneration line
export const REGENERATION_Y = 0.08;

// X-axis range
export const X_MIN = 0;
export const X_MAX = 20;

// Cycle tick positions for reset arrows (every 2 cycles)
export const CYCLE_TICKS = [2, 4, 6, 8, 10, 12, 14, 16, 18, 20];
