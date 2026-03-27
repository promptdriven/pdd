// ── Colors ──────────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.08;
export const AXIS_COLOR = "#334155";
export const AXIS_LABEL_COLOR = "#94A3B8";
export const LABOR_LINE_COLOR = "#D9944A";
export const GARMENT_LINE_COLOR = "#4A90D9";
export const THRESHOLD_LABEL_COLOR = "#E2E8F0";
export const DARNING_SENSE_COLOR = "#5AAA6E";
export const DARNING_IRRATIONAL_COLOR = "#EF4444";
export const CROSSING_GLOW_COLOR = "#FFFFFF";

// ── Chart Layout ────────────────────────────────────────────────
export const CHART_LEFT = 160;
export const CHART_TOP = 80;
export const CHART_RIGHT = 1800;
export const CHART_BOTTOM = 960;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// ── Axis Ranges ─────────────────────────────────────────────────
export const X_MIN = 1950;
export const X_MAX = 2020;
export const Y_MIN = 0;
export const Y_MAX = 1;

// ── Line Thickness ──────────────────────────────────────────────
export const LINE_STROKE_WIDTH = 3;
export const AXIS_STROKE_WIDTH = 1.5;

// ── Data Points (authoritative from spec JSON) ──────────────────
export const LABOR_COST_DATA = [
  { x: 1950, y: 0.2 },
  { x: 1960, y: 0.35 },
  { x: 1970, y: 0.5 },
  { x: 1980, y: 0.6 },
  { x: 1990, y: 0.7 },
  { x: 2000, y: 0.78 },
  { x: 2010, y: 0.82 },
  { x: 2020, y: 0.85 },
];

export const GARMENT_COST_DATA = [
  { x: 1950, y: 0.8 },
  { x: 1960, y: 0.5 },
  { x: 1965, y: 0.35 },
  { x: 1970, y: 0.25 },
  { x: 1980, y: 0.18 },
  { x: 1990, y: 0.12 },
  { x: 2000, y: 0.1 },
  { x: 2020, y: 0.08 },
];

// ── Crossing Point ──────────────────────────────────────────────
export const CROSSING_YEAR = 1962;

// ── Animation Frame Ranges ──────────────────────────────────────
export const AXES_DRAW_START = 0;
export const AXES_DRAW_END = 30;
export const LINES_DRAW_START = 30;
export const LINES_DRAW_END = 600;
export const CROSSING_FRAME = 150;
export const THRESHOLD_LABEL_START = 150;
export const THRESHOLD_LABEL_END = 180;
export const ZONE_LABEL_START = 180;
export const ZONE_LABEL_DURATION = 20;
export const MORPH_START = 600;
export const MORPH_END = 720;
export const TOTAL_FRAMES = 720;

// ── Helpers ─────────────────────────────────────────────────────
/** Map a data x value to pixel x within the chart area */
export const xToPixel = (x: number): number =>
  CHART_LEFT + ((x - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;

/** Map a data y value to pixel y within the chart area (y inverted) */
export const yToPixel = (y: number): number =>
  CHART_BOTTOM - ((y - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;

/**
 * Linearly interpolate between data points for a given x.
 */
export const interpolateData = (
  data: { x: number; y: number }[],
  targetX: number
): number => {
  if (targetX <= data[0].x) return data[0].y;
  if (targetX >= data[data.length - 1].x) return data[data.length - 1].y;
  for (let i = 0; i < data.length - 1; i++) {
    if (targetX >= data[i].x && targetX <= data[i + 1].x) {
      const t = (targetX - data[i].x) / (data[i + 1].x - data[i].x);
      return data[i].y + t * (data[i + 1].y - data[i].y);
    }
  }
  return data[data.length - 1].y;
};
