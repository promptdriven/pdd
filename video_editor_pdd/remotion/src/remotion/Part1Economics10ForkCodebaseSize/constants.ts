// === COLORS ===
export const BG_COLOR = "#0A0F1A";
export const AXIS_COLOR = "#475569";
export const AXIS_LABEL_COLOR = "#94A3B8";
export const GRID_COLOR = "#1E293B";

// Chart line colors
export const GENERATE_LINE_COLOR = "#3B82F6";
export const PATCH_LINE_COLOR = "#F59E0B";
export const SMALL_CODEBASE_COLOR = "#5AAA6E";
export const LARGE_CODEBASE_COLOR = "#EF4444";
export const ARROW_COLOR = "#F59E0B";
export const CONTEXT_LABEL_COLOR = "#94A3B8";

// Debt area
export const DEBT_AREA_COLOR = "rgba(239, 68, 68, 0.08)";

// === DIMENSIONS ===
export const WIDTH = 1920;
export const HEIGHT = 1080;

// Chart area
export const CHART_LEFT = 160;
export const CHART_RIGHT = 1760;
export const CHART_TOP = 100;
export const CHART_BOTTOM = 900;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// === DATA ===
// X-axis: years 2013-2026
export const X_MIN = 2013;
export const X_MAX = 2026;

// Y-axis: cost in developer hours (normalized 0-1 scale representing 0-20 hours)
export const Y_MIN = 0;
export const Y_MAX = 1.0;
export const Y_HOUR_MAX = 20; // for axis labels

// Generate line (blue) — cost of writing new code from scratch
export const GENERATE_LINE_DATA = [
  { x: 2013, y: 0.90 },
  { x: 2016, y: 0.85 },
  { x: 2018, y: 0.78 },
  { x: 2020, y: 0.55 },
  { x: 2022, y: 0.30 },
  { x: 2024, y: 0.15 },
  { x: 2026, y: 0.08 },
];

// Patch/maintain line (amber) — cost of patching existing code, before fork
export const PATCH_LINE_DATA = [
  { x: 2013, y: 0.15 },
  { x: 2016, y: 0.22 },
  { x: 2018, y: 0.35 },
  { x: 2020, y: 0.48 },
];

// Fork data
export const FORK_POINT = { x: 2020, y: 0.48 };

export const SMALL_CODEBASE_DATA = [
  { x: 2020, y: 0.48 },
  { x: 2022, y: 0.30 },
  { x: 2024, y: 0.18 },
  { x: 2026, y: 0.10 },
];

export const LARGE_CODEBASE_DATA = [
  { x: 2020, y: 0.48 },
  { x: 2022, y: 0.47 },
  { x: 2024, y: 0.46 },
  { x: 2026, y: 0.45 },
];

// === ANIMATION TIMING (frames) ===
export const TOTAL_FRAMES = 1380;

// Phase 1: Chart visible (0-90)
export const CHART_APPEAR_END = 90;

// Phase 2: Fork begins (90-210)
export const FORK_START = 90;
export const FORK_DIVERGE_END = 210;
export const CONTEXT_LABEL_APPEAR = 180;

// Phase 3: Fork diverges further (210-420)
export const FORK_EXTEND_END = 420;

// Phase 4: Annotations (420-600)
export const METR_ANNOTATION_START = 420;
export const BELIEF_ANNOTATION_START = 540;

// Phase 5: Hold on annotations (600-900)

// Phase 6: Trap arrow (900-1050)
export const ARROW_DRAW_START = 900;
export const ARROW_DRAW_END = 990; // 90 frames
export const ARROW_LABEL_START = 960;

// Phase 7: Hold (1050-1380)

// === HELPERS ===
export function mapX(xVal: number): number {
  return CHART_LEFT + ((xVal - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;
}

export function mapY(yVal: number): number {
  return CHART_BOTTOM - ((yVal - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;
}

export function dataToPath(data: { x: number; y: number }[]): string {
  return data
    .map((pt, i) => `${i === 0 ? "M" : "L"} ${mapX(pt.x)} ${mapY(pt.y)}`)
    .join(" ");
}

// Cubic bezier path for smoother curves
export function dataToCurvePath(data: { x: number; y: number }[]): string {
  if (data.length < 2) return "";
  const points = data.map((pt) => ({ x: mapX(pt.x), y: mapY(pt.y) }));
  let path = `M ${points[0].x} ${points[0].y}`;
  for (let i = 1; i < points.length; i++) {
    const prev = points[i - 1];
    const curr = points[i];
    const cpx1 = prev.x + (curr.x - prev.x) * 0.5;
    const cpy1 = prev.y;
    const cpx2 = prev.x + (curr.x - prev.x) * 0.5;
    const cpy2 = curr.y;
    path += ` C ${cpx1} ${cpy1}, ${cpx2} ${cpy2}, ${curr.x} ${curr.y}`;
  }
  return path;
}
