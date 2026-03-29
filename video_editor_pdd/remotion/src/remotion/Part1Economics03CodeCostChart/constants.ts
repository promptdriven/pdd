// ── Colors ──────────────────────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.08;
export const AXIS_COLOR = "#334155";
export const LABEL_COLOR = "#94A3B8";
export const BLUE_LINE_COLOR = "#4A90D9";
export const AMBER_LINE_COLOR = "#D9944A";
export const DEBT_FILL_COLOR = "#D9944A";
export const DEBT_FILL_OPACITY = 0.12;
export const MARKER_LINE_COLOR = "#64748B";

// ── Dimensions ──────────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// Chart area (padded within canvas)
export const CHART_LEFT = 140;
export const CHART_RIGHT = 1800;
export const CHART_TOP = 80;
export const CHART_BOTTOM = 960;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// Grid
export const GRID_SPACING = 150; // px between horizontal grid lines

// ── Axis ranges ─────────────────────────────────────────────────────────────
export const X_MIN = 2000;
export const X_MAX = 2026;
export const Y_MIN = 0;
export const Y_MAX = 1.0;

// ── Data series ─────────────────────────────────────────────────────────────
export interface DataPoint {
  x: number;
  y: number;
}

export const GENERATE_COST_DATA: DataPoint[] = [
  { x: 2000, y: 0.9 },
  { x: 2010, y: 0.88 },
  { x: 2020, y: 0.85 },
  { x: 2021, y: 0.82 },
  { x: 2022, y: 0.78 },
  { x: 2023, y: 0.65 },
  { x: 2024, y: 0.35 },
  { x: 2025, y: 0.18 },
  { x: 2026, y: 0.1 },
];

export const IMMEDIATE_PATCH_DATA: DataPoint[] = [
  { x: 2000, y: 0.55 },
  { x: 2010, y: 0.52 },
  { x: 2020, y: 0.48 },
  { x: 2021, y: 0.42 },
  { x: 2022, y: 0.35 },
  { x: 2023, y: 0.28 },
  { x: 2024, y: 0.22 },
  { x: 2025, y: 0.18 },
  { x: 2026, y: 0.15 },
];

export const TOTAL_COST_DEBT_DATA: DataPoint[] = [
  { x: 2000, y: 0.6 },
  { x: 2010, y: 0.62 },
  { x: 2020, y: 0.65 },
  { x: 2021, y: 0.66 },
  { x: 2022, y: 0.68 },
  { x: 2023, y: 0.7 },
  { x: 2024, y: 0.72 },
  { x: 2025, y: 0.73 },
  { x: 2026, y: 0.74 },
];

// ── Date markers ────────────────────────────────────────────────────────────
export interface DateMarker {
  year: number;
  label: string;
}

export const DATE_MARKERS: DateMarker[] = [
  { year: 2021, label: "Codex" },
  { year: 2023, label: "GPT-4" },
  { year: 2023.5, label: "Claude" },
  { year: 2024, label: "Gemini" },
];

// ── Animation frame ranges ──────────────────────────────────────────────────
export const TOTAL_FRAMES = 1650;

// Phase 1: Axes draw
export const AXES_START = 0;
export const AXES_END = 45;

// Phase 2: Blue line draws (2000 → 2026)
export const BLUE_LINE_START = 45;
export const BLUE_LINE_END = 300;

// Phase 3: Amber solid line draws
export const AMBER_SOLID_START = 300;
export const AMBER_SOLID_END = 450;

// Phase 4: Focus pulse on amber solid
export const PULSE_START = 450;
export const PULSE_END = 540;

// Phase 5: Dashed line + debt area
export const DASHED_START = 540;
export const DASHED_END = 600;

// Phase 6: Camera pullback
export const PULLBACK_START = 600;
export const PULLBACK_END = 690; // 90 frames
export const PULLBACK_SCALE_FROM = 1.0;
export const PULLBACK_SCALE_TO = 0.85;

// Phase 7: Hold
export const HOLD_START = 690;

// ── Helper: map data coords to pixel coords ─────────────────────────────────
export function dataToPixelX(xVal: number): number {
  return CHART_LEFT + ((xVal - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;
}

export function dataToPixelY(yVal: number): number {
  return CHART_BOTTOM - ((yVal - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;
}

// ── Helper: interpolate between data points at a given x ────────────────────
export function interpolateY(data: DataPoint[], xVal: number): number {
  if (xVal <= data[0].x) return data[0].y;
  if (xVal >= data[data.length - 1].x) return data[data.length - 1].y;
  for (let i = 0; i < data.length - 1; i++) {
    if (xVal >= data[i].x && xVal <= data[i + 1].x) {
      const t = (xVal - data[i].x) / (data[i + 1].x - data[i].x);
      return data[i].y + t * (data[i + 1].y - data[i].y);
    }
  }
  return data[data.length - 1].y;
}

// ── Helper: build SVG path from data points ─────────────────────────────────
export function buildPathD(data: DataPoint[]): string {
  return data
    .map((pt, i) => {
      const px = dataToPixelX(pt.x);
      const py = dataToPixelY(pt.y);
      return `${i === 0 ? "M" : "L"} ${px} ${py}`;
    })
    .join(" ");
}

// ── Helper: compute total SVG path length (approximation for strokeDasharray) ─
export function computePathLength(data: DataPoint[]): number {
  let len = 0;
  for (let i = 1; i < data.length; i++) {
    const dx = dataToPixelX(data[i].x) - dataToPixelX(data[i - 1].x);
    const dy = dataToPixelY(data[i].y) - dataToPixelY(data[i - 1].y);
    len += Math.sqrt(dx * dx + dy * dy);
  }
  return len;
}
