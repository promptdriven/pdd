// constants.ts — Colors, dimensions, data points for Code Cost Chart

// === COLORS ===
export const BG_COLOR = "#0A0F1A";
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.08;
export const AXIS_COLOR = "#334155";
export const AXIS_LABEL_COLOR = "#94A3B8";
export const GENERATE_LINE_COLOR = "#4A90D9";
export const PATCH_LINE_COLOR = "#D9944A";
export const DEBT_FILL_COLOR = "#D9944A";
export const DEBT_FILL_OPACITY = 0.12;
export const MARKER_LINE_COLOR = "#64748B";

// === DIMENSIONS ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const CHART_LEFT = 160;
export const CHART_RIGHT = 1760;
export const CHART_TOP = 100;
export const CHART_BOTTOM = 920;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;
export const GRID_SPACING = 150;

// === AXIS RANGES ===
export const X_MIN = 2000;
export const X_MAX = 2026;
export const Y_MIN = 0;
export const Y_MAX = 1.0;

// === ANIMATION FRAMES ===
export const AXES_DRAW_START = 0;
export const AXES_DRAW_END = 45;
export const BLUE_LINE_START = 45;
export const BLUE_LINE_END = 300;
export const AMBER_SOLID_START = 300;
export const AMBER_SOLID_END = 450;
export const PULSE_START = 450;
export const PULSE_END = 540;
export const DASHED_LINE_START = 540;
export const DASHED_LINE_END = 600;
export const PULLBACK_START = 600;
export const PULLBACK_END = 690; // 90 frames for pullback
export const HOLD_START = 690;
export const TOTAL_FRAMES = 1650;

// === DATA SERIES ===
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

// === DATE MARKERS ===
export interface DateMarkerDef {
  year: number;
  label: string;
}

export const DATE_MARKERS: DateMarkerDef[] = [
  { year: 2021, label: "Codex" },
  { year: 2023, label: "GPT-4" },
  { year: 2023.5, label: "Claude" },
  { year: 2024, label: "Gemini" },
];

// === LEGEND ITEMS ===
export interface LegendItemDef {
  label: string;
  color: string;
  dashed: boolean;
}

export const LEGEND_ITEMS: LegendItemDef[] = [
  { label: "Cost to generate", color: GENERATE_LINE_COLOR, dashed: false },
  { label: "Immediate patch cost", color: PATCH_LINE_COLOR, dashed: false },
  { label: "Total cost (with debt)", color: PATCH_LINE_COLOR, dashed: true },
];

// === HELPER FUNCTIONS ===
export function mapX(year: number): number {
  return CHART_LEFT + ((year - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;
}

export function mapY(value: number): number {
  return CHART_BOTTOM - ((value - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;
}

export function dataToSvgPath(data: DataPoint[]): string {
  return data
    .map((pt, i) => {
      const px = mapX(pt.x);
      const py = mapY(pt.y);
      return `${i === 0 ? "M" : "L"} ${px} ${py}`;
    })
    .join(" ");
}

export function dataToSvgPolygon(
  upperData: DataPoint[],
  lowerData: DataPoint[]
): string {
  const upper = upperData.map((pt) => `${mapX(pt.x)},${mapY(pt.y)}`).join(" ");
  const lower = [...lowerData]
    .reverse()
    .map((pt) => `${mapX(pt.x)},${mapY(pt.y)}`)
    .join(" ");
  return `${upper} ${lower}`;
}
