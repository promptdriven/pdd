// Part1Economics03CodeCostTripleLine constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0D1117";

// Chart area padding (spec: 280px left, 100px right, 140px top, 120px bottom)
export const PADDING_LEFT = 280;
export const PADDING_RIGHT = 100;
export const PADDING_TOP = 140;
export const PADDING_BOTTOM = 120;

// Derived chart region
export const CHART_X = PADDING_LEFT;
export const CHART_Y = PADDING_TOP;
export const CHART_W = WIDTH - PADDING_LEFT - PADDING_RIGHT; // 1540
export const CHART_H = HEIGHT - PADDING_TOP - PADDING_BOTTOM; // 820

// X-axis: 2015–2025
export const X_MIN = 2015;
export const X_MAX = 2025;
export const X_RANGE = X_MAX - X_MIN; // 10

// Y-axis: 0–20 developer hours
export const Y_MIN = 0;
export const Y_MAX = 20;

// Colors
export const BLUE_LINE_COLOR = "#4A90D9";
export const AMBER_LINE_COLOR = "#D9944A";
export const AXIS_COLOR = "#334155";
export const AXIS_LABEL_COLOR = "#94A3B8";
export const GRID_COLOR = "#334155";

// Line widths
export const BLUE_STROKE_WIDTH = 3;
export const AMBER_SOLID_STROKE_WIDTH = 3;
export const AMBER_DASHED_STROKE_WIDTH = 2;

// Typography
export const FONT_FAMILY = "Inter, sans-serif";

// Animation frames (at 30fps, total 1050)
export const TOTAL_FRAMES = 1050;

// Act 1: Chart morph (axes relabel)
export const MORPH_START = 0;
export const MORPH_END = 30;

// Act 2: AI milestone markers fade in
export const MILESTONE_START = 30;
export const MILESTONE_END = 60;

// Act 3: Blue "generate" line draws
export const BLUE_LINE_START = 60;
export const BLUE_LINE_END = 180;

// Act 4: Amber solid "immediate patch" line draws
export const AMBER_SOLID_START = 180;
export const AMBER_SOLID_END = 300;

// Act 5: Amber dashed "total cost" line draws
export const AMBER_DASHED_START = 300;
export const AMBER_DASHED_END = 420;

// Act 6: Debt shaded area fills
export const DEBT_FILL_START = 420;
export const DEBT_FILL_END = 540;

// Act 7: Hold with pulse (540–720)
// Act 8: Hold for narration (720–1050)

// Debt area pulse cycle
export const DEBT_PULSE_CYCLE = 60; // frames per cycle
export const DEBT_OPACITY_MIN = 0.08;
export const DEBT_OPACITY_MAX = 0.12;

// AI milestones
export const MILESTONES = [
  { year: 2021, label: "Codex" },
  { year: 2022, label: "Copilot" },
  { year: 2023, label: "GPT-4 / Claude" },
  { year: 2024, label: "Cursor / Claude Code" },
];

// Data: Cost to generate (blue)
export const GENERATE_COST_DATA = [
  { x: 2015, y: 18 },
  { x: 2018, y: 17.5 },
  { x: 2020, y: 17 },
  { x: 2021, y: 16 },
  { x: 2022, y: 14 },
  { x: 2023, y: 10 },
  { x: 2024, y: 6 },
  { x: 2025, y: 4 },
];

// Data: Immediate patch cost (amber solid)
export const PATCH_COST_DATA = [
  { x: 2015, y: 8 },
  { x: 2018, y: 7.5 },
  { x: 2020, y: 7 },
  { x: 2021, y: 6 },
  { x: 2022, y: 5 },
  { x: 2023, y: 4 },
  { x: 2024, y: 3 },
  { x: 2025, y: 2 },
];

// Data: Total cost with debt (amber dashed)
export const TOTAL_COST_DATA = [
  { x: 2015, y: 14 },
  { x: 2018, y: 14 },
  { x: 2020, y: 13.5 },
  { x: 2021, y: 13.5 },
  { x: 2022, y: 13 },
  { x: 2023, y: 13 },
  { x: 2024, y: 13 },
  { x: 2025, y: 13 },
];

// Helpers to convert data coordinates to pixel coordinates
export function dataToPixelX(year: number): number {
  return CHART_X + ((year - X_MIN) / X_RANGE) * CHART_W;
}

export function dataToPixelY(hours: number): number {
  return CHART_Y + CHART_H * (1 - hours / Y_MAX);
}
