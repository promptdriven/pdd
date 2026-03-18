// ─── Colors ───────────────────────────────────────────────────────────
export const BG_COLOR = "#0D1117";
export const AMBER_SOLID = "#D9944A";
export const AMBER_DASHED = "#D9944A";
export const BLUE_GENERATE = "#4A90D9";
export const GREEN_SMALL = "#5AAA6E";
export const RED_LARGE = "#E74C3C";
export const SLATE_ANNOTATION = "#94A3B8";
export const AXIS_COLOR = "#94A3B8";
export const GRID_COLOR = "#1E293B";

// ─── Canvas / Chart Layout ───────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;

export const CHART_LEFT = 140;
export const CHART_RIGHT = 1780;
export const CHART_TOP = 80;
export const CHART_BOTTOM = 920;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// ─── Axes ranges ─────────────────────────────────────────────────────
export const X_MIN = 2015;
export const X_MAX = 2025;
export const Y_MIN = 0;
export const Y_MAX = 20; // Developer hours

// ─── Helpers: data → pixel ───────────────────────────────────────────
export function xToPixel(year: number): number {
  return CHART_LEFT + ((year - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;
}

export function yToPixel(hours: number): number {
  return CHART_BOTTOM - ((hours - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;
}

// ─── Original three-line chart data ──────────────────────────────────
// Immediate patch cost (solid amber) — pre-fork single line
export const PATCH_COST_DATA = [
  { x: 2015, y: 8 },
  { x: 2016, y: 7.5 },
  { x: 2017, y: 7.2 },
  { x: 2018, y: 7 },
  { x: 2019, y: 7 },
  { x: 2020, y: 7 },
];

// Total cost with debt (dashed amber) — rises over time
export const TOTAL_COST_DATA = [
  { x: 2015, y: 10 },
  { x: 2016, y: 10.5 },
  { x: 2017, y: 11 },
  { x: 2018, y: 12 },
  { x: 2019, y: 13 },
  { x: 2020, y: 14 },
  { x: 2021, y: 15 },
  { x: 2022, y: 16 },
  { x: 2023, y: 17 },
  { x: 2024, y: 18 },
  { x: 2025, y: 19 },
];

// Generation cost (blue) — starts high, plunges
export const GENERATE_COST_DATA = [
  { x: 2015, y: 18 },
  { x: 2016, y: 17 },
  { x: 2017, y: 16 },
  { x: 2018, y: 15 },
  { x: 2019, y: 14 },
  { x: 2020, y: 12 },
  { x: 2021, y: 9 },
  { x: 2022, y: 6 },
  { x: 2023, y: 3.5 },
  { x: 2024, y: 1.5 },
  { x: 2025, y: 0.5 },
];

// ─── Forked line data ────────────────────────────────────────────────
export const SMALL_CODEBASE_DATA = [
  { x: 2020, y: 7 },
  { x: 2021, y: 5 },
  { x: 2022, y: 4 },
  { x: 2023, y: 2.5 },
  { x: 2024, y: 2 },
  { x: 2025, y: 1 },
];

export const LARGE_CODEBASE_DATA = [
  { x: 2020, y: 7 },
  { x: 2021, y: 8.5 },
  { x: 2022, y: 10 },
  { x: 2023, y: 10.5 },
  { x: 2024, y: 11 },
  { x: 2025, y: 12 },
];

// ─── AI Milestone markers ────────────────────────────────────────────
export const AI_MILESTONES = [
  { year: 2017, label: "Transformer" },
  { year: 2020, label: "GPT-3" },
  { year: 2021, label: "Codex" },
  { year: 2022, label: "ChatGPT" },
  { year: 2023, label: "GPT-4" },
  { year: 2024, label: "Claude 3.5" },
];

// ─── Animation Frames ────────────────────────────────────────────────
export const TOTAL_FRAMES = 750;
export const FPS = 30;

// Phase timing
export const PHASE_CHART_IN = { start: 0, end: 60 };
export const PHASE_FORK = { start: 60, end: 180 };
export const PHASE_ANNOTATION = { start: 180, end: 240 };
export const PHASE_METR = { start: 240, end: 330 };
export const PHASE_ARROW = { start: 330, end: 390 };
export const PHASE_CROSSING = { start: 390, end: 480 };
export const PHASE_WE_ARE_HERE = { start: 480, end: 540 };
export const PHASE_PROMPT_NOTE = { start: 540, end: 600 };
export const PHASE_HOLD = { start: 600, end: 750 };
