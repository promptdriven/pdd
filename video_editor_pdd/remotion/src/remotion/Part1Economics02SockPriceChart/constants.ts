// ── Colors ──────────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.08;
export const AXIS_COLOR = "#334155";
export const AXIS_LABEL_COLOR = "#94A3B8";
export const LABOR_COLOR = "#D9944A";
export const GARMENT_COLOR = "#4A90D9";
export const THRESHOLD_LABEL_COLOR = "#E2E8F0";
export const DARNING_SENSE_COLOR = "#5AAA6E";
export const DARNING_IRRATIONAL_COLOR = "#EF4444";
export const GLOW_COLOR = "#FFFFFF";

// ── Dimensions ──────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// Chart area (padded within canvas)
export const CHART_LEFT = 180;
export const CHART_RIGHT = 1780;
export const CHART_TOP = 100;
export const CHART_BOTTOM = 920;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// ── Axis config ─────────────────────────────────────────────────
export const X_MIN = 1950;
export const X_MAX = 2020;
export const X_TICK_INTERVAL = 10;
export const Y_MIN = 0;
export const Y_MAX = 1;

// ── Data ────────────────────────────────────────────────────────
export interface DataPoint {
  x: number;
  y: number;
}

export const LABOR_COST_DATA: DataPoint[] = [
  { x: 1950, y: 0.2 },
  { x: 1960, y: 0.35 },
  { x: 1970, y: 0.5 },
  { x: 1980, y: 0.6 },
  { x: 1990, y: 0.7 },
  { x: 2000, y: 0.78 },
  { x: 2010, y: 0.82 },
  { x: 2020, y: 0.85 },
];

export const GARMENT_COST_DATA: DataPoint[] = [
  { x: 1950, y: 0.8 },
  { x: 1960, y: 0.5 },
  { x: 1965, y: 0.35 },
  { x: 1970, y: 0.25 },
  { x: 1980, y: 0.18 },
  { x: 1990, y: 0.12 },
  { x: 2000, y: 0.1 },
  { x: 2020, y: 0.08 },
];

// Crossing point (pre-computed via linear interpolation between 1960 data points)
// Labor: 0.35 at 1960, 0.5 at 1970 → y at 1962 = 0.35 + 0.015*2 = 0.38
// Garment: 0.5 at 1960, 0.35 at 1965 → y at 1962 = 0.5 - 0.03*2 = 0.44
// Actual intersection solve: labor slope 0.015/yr, garment slope -0.03/yr from 1960
// 0.35 + 0.015t = 0.5 - 0.03t → 0.045t = 0.15 → t ≈ 3.33 → year ≈ 1963.3, y ≈ 0.4
export const CROSSING_YEAR = 1963;
export const CROSSING_Y = 0.4;

// ── Animation timing (frames) ───────────────────────────────────
export const TOTAL_FRAMES = 720;
export const FPS = 30;

// Phase 1: Axes draw in
export const AXES_START = 0;
export const AXES_END = 30;

// Phase 2-3: Lines drawing (from 1950 to crossing)
export const LINES_START = 30;
export const LINES_CROSS_FRAME = 150;

// Phase 4: Crossing highlight
export const CROSSING_HIGHLIGHT_START = 150;
export const CROSSING_HIGHLIGHT_END = 180;

// Phase 5: Post-crossing divergence + irrational label
export const DIVERGE_START = 180;
export const IRRATIONAL_LABEL_START = 200;

// Phase 6: Lines reach 2020
export const LINES_END = 600;

// Phase 7: Morph / fade transition
export const MORPH_START = 600;
export const MORPH_END = 720;

// ── Typography ──────────────────────────────────────────────────
export const FONT_FAMILY = "Inter, sans-serif";
export const AXIS_FONT_SIZE = 14;
export const THRESHOLD_FONT_SIZE = 18;
export const ZONE_FONT_SIZE = 13;
export const AXIS_LABEL_OPACITY = 0.6;
export const ZONE_LABEL_OPACITY = 0.6;

// ── Line config ─────────────────────────────────────────────────
export const LINE_STROKE_WIDTH = 3;
export const GLOW_RADIUS = 20;
export const GLOW_OPACITY = 0.15;

// ── Helpers ─────────────────────────────────────────────────────
/** Convert a data x-value (year) to canvas pixel x */
export function xToPixel(year: number): number {
  return CHART_LEFT + ((year - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;
}

/** Convert a data y-value (0-1, where 0 = bottom) to canvas pixel y.
 *  Note: canvas y is inverted (0 at top). y=1 → CHART_TOP, y=0 → CHART_BOTTOM */
export function yToPixel(value: number): number {
  return CHART_BOTTOM - value * CHART_HEIGHT;
}

/** Linearly interpolate data series at a given x */
export function interpolateY(data: DataPoint[], atX: number): number {
  if (atX <= data[0].x) return data[0].y;
  if (atX >= data[data.length - 1].x) return data[data.length - 1].y;
  for (let i = 0; i < data.length - 1; i++) {
    if (atX >= data[i].x && atX <= data[i + 1].x) {
      const t = (atX - data[i].x) / (data[i + 1].x - data[i].x);
      return data[i].y + t * (data[i + 1].y - data[i].y);
    }
  }
  return data[data.length - 1].y;
}
