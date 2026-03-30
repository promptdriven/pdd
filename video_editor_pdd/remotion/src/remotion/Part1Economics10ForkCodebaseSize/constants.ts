// ── Colors ──────────────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const AXIS_COLOR = "#475569";
export const AXIS_LABEL_COLOR = "#94A3B8";
export const GRID_COLOR = "#1E293B";

// Line colors
export const AMBER_LINE_COLOR = "#F59E0B"; // pre-fork patch line
export const GREEN_LINE_COLOR = "#5AAA6E"; // small codebase fork
export const RED_LINE_COLOR = "#EF4444"; // large codebase fork
export const BLUE_LINE_COLOR = "#3B82F6"; // generate line (background)
export const DEBT_AREA_COLOR = "rgba(239, 68, 68, 0.08)";

// Annotation / arrow
export const ARROW_COLOR = "#F59E0B";
export const CONTEXT_LABEL_COLOR = "#94A3B8";

// ── Typography ──────────────────────────────────────────────────────
export const FONT_FAMILY = "Inter, system-ui, -apple-system, sans-serif";

// ── Canvas & chart layout ───────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;

export const CHART_LEFT = 160;
export const CHART_RIGHT = 1760;
export const CHART_TOP = 120;
export const CHART_BOTTOM = 900;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// ── Axis ranges ─────────────────────────────────────────────────────
export const X_MIN = 2014;
export const X_MAX = 2026;
export const Y_MIN = 0;
export const Y_MAX = 1.0;

// ── Data ────────────────────────────────────────────────────────────

/** "Code generation" baseline (blue) – visible for context */
export const GENERATE_LINE_DATA = [
  { x: 2014, y: 0.95 },
  { x: 2016, y: 0.85 },
  { x: 2018, y: 0.70 },
  { x: 2020, y: 0.40 },
  { x: 2022, y: 0.20 },
  { x: 2024, y: 0.08 },
  { x: 2026, y: 0.03 },
];

/** Patch line before fork */
export const PATCH_LINE_DATA = [
  { x: 2014, y: 0.90 },
  { x: 2016, y: 0.78 },
  { x: 2018, y: 0.62 },
  { x: 2020, y: 0.48 },
];

/** Small codebase fork (green, drops) */
export const SMALL_CODEBASE_DATA = [
  { x: 2020, y: 0.48 },
  { x: 2022, y: 0.30 },
  { x: 2024, y: 0.18 },
  { x: 2026, y: 0.10 },
];

/** Large codebase fork (red, flat) */
export const LARGE_CODEBASE_DATA = [
  { x: 2020, y: 0.48 },
  { x: 2022, y: 0.47 },
  { x: 2024, y: 0.46 },
  { x: 2026, y: 0.45 },
];

// ── Timing (frames @ 30 fps) ────────────────────────────────────────
export const TOTAL_FRAMES = 1380;

export const CHART_APPEAR_END = 90;
export const FORK_START = 90;
export const FORK_ANIM_DURATION = 120;
export const CONTEXT_LABEL_FRAME = 180;
export const ANNOTATION_1_FRAME = 420;
export const ANNOTATION_2_FRAME = 540;
export const ARROW_START = 900;
export const ARROW_DRAW_DURATION = 90;
export const ARROW_LABEL_FRAME = 990;

// ── Helpers ─────────────────────────────────────────────────────────
export function xToPixel(xVal: number): number {
  return CHART_LEFT + ((xVal - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;
}

export function yToPixel(yVal: number): number {
  return CHART_BOTTOM - ((yVal - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;
}

export interface DataPoint {
  x: number;
  y: number;
}

export function dataToSvgPath(data: DataPoint[]): string {
  return data
    .map((pt, i) => {
      const px = xToPixel(pt.x);
      const py = yToPixel(pt.y);
      return i === 0 ? `M ${px} ${py}` : `L ${px} ${py}`;
    })
    .join(" ");
}

/** Smooth cubic-bezier path for data points */
export function dataToSmoothPath(data: DataPoint[]): string {
  if (data.length < 2) return "";
  const points = data.map((pt) => ({ x: xToPixel(pt.x), y: yToPixel(pt.y) }));

  let path = `M ${points[0].x} ${points[0].y}`;
  for (let i = 1; i < points.length; i++) {
    const prev = points[i - 1];
    const curr = points[i];
    const cpx = (prev.x + curr.x) / 2;
    path += ` C ${cpx} ${prev.y}, ${cpx} ${curr.y}, ${curr.x} ${curr.y}`;
  }
  return path;
}
