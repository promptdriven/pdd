// === Colors ===
export const BG_COLOR = "#0D1117";
export const AXIS_COLOR = "#334155";
export const LABEL_COLOR = "#94A3B8";
export const BLUE_LINE = "#4A90D9";
export const AMBER_LINE = "#D9944A";
export const GRID_COLOR = "#334155";

// === Chart Dimensions ===
export const CANVAS_W = 1920;
export const CANVAS_H = 1080;
export const MARGIN = { top: 140, right: 100, bottom: 120, left: 280 };
export const CHART_W = CANVAS_W - MARGIN.left - MARGIN.right;
export const CHART_H = CANVAS_H - MARGIN.top - MARGIN.bottom;

// === Axis Ranges ===
export const X_MIN = 2015;
export const X_MAX = 2025;
export const Y_MIN = 0;
export const Y_MAX = 20;
export const Y_MAJOR = 5;

// === Data Series ===
export interface DataPoint {
  x: number;
  y: number;
}

export const GENERATE_COST_DATA: DataPoint[] = [
  { x: 2015, y: 18 },
  { x: 2018, y: 17.5 },
  { x: 2020, y: 17 },
  { x: 2021, y: 16 },
  { x: 2022, y: 14 },
  { x: 2023, y: 10 },
  { x: 2024, y: 6 },
  { x: 2025, y: 4 },
];

export const PATCH_COST_DATA: DataPoint[] = [
  { x: 2015, y: 8 },
  { x: 2018, y: 7.5 },
  { x: 2020, y: 7 },
  { x: 2021, y: 6 },
  { x: 2022, y: 5 },
  { x: 2023, y: 4 },
  { x: 2024, y: 3 },
  { x: 2025, y: 2 },
];

export const TOTAL_COST_DATA: DataPoint[] = [
  { x: 2015, y: 14 },
  { x: 2018, y: 14 },
  { x: 2020, y: 13.5 },
  { x: 2021, y: 13.5 },
  { x: 2022, y: 13 },
  { x: 2023, y: 13 },
  { x: 2024, y: 13 },
  { x: 2025, y: 13 },
];

// === Milestones ===
export interface Milestone {
  x: number;
  label: string;
}

export const MILESTONES: Milestone[] = [
  { x: 2021, label: "Codex" },
  { x: 2022, label: "Copilot" },
  { x: 2023, label: "GPT-4 / Claude" },
  { x: 2024, label: "Cursor / Claude Code" },
];

// === Animation Frames ===
export const TOTAL_FRAMES = 1050;
export const MORPH_START = 0;
export const MORPH_END = 30;
export const MILESTONE_START = 30;
export const MILESTONE_FADE_DUR = 10;
export const BLUE_LINE_START = 60;
export const BLUE_LINE_DUR = 120;
export const AMBER_SOLID_START = 180;
export const AMBER_SOLID_DUR = 120;
export const AMBER_DASH_START = 300;
export const AMBER_DASH_DUR = 120;
export const DEBT_FILL_START = 420;
export const DEBT_FILL_DUR = 120;
export const PULSE_START = 540;
export const PULSE_CYCLE = 60;

// === Helpers ===
/** Map data x to pixel x within chart area */
export function xToPixel(val: number): number {
  return ((val - X_MIN) / (X_MAX - X_MIN)) * CHART_W;
}

/** Map data y to pixel y within chart area (inverted) */
export function yToPixel(val: number): number {
  return CHART_H - ((val - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_H;
}

/** Build an SVG path "d" string from data points */
export function buildPathD(data: DataPoint[]): string {
  return data
    .map((pt, i) => {
      const px = xToPixel(pt.x);
      const py = yToPixel(pt.y);
      return `${i === 0 ? "M" : "L"} ${px} ${py}`;
    })
    .join(" ");
}

/** Build a closed polygon path for the shaded area between two series */
export function buildAreaD(upper: DataPoint[], lower: DataPoint[]): string {
  const forwardPath = lower
    .map((pt, i) => {
      const px = xToPixel(pt.x);
      const py = yToPixel(pt.y);
      return `${i === 0 ? "M" : "L"} ${px} ${py}`;
    })
    .join(" ");

  const reversePath = [...upper]
    .reverse()
    .map((pt) => {
      const px = xToPixel(pt.x);
      const py = yToPixel(pt.y);
      return `L ${px} ${py}`;
    })
    .join(" ");

  return `${forwardPath} ${reversePath} Z`;
}
