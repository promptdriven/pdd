// Part1Economics09CrossingLinesMoment constants
// Consistent with Part1Economics03CodeCostTripleLine chart layout

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0D1117";

// Chart area padding (matches spec 03)
export const PADDING_LEFT = 280;
export const PADDING_RIGHT = 100;
export const PADDING_TOP = 140;
export const PADDING_BOTTOM = 120;

// Derived chart region
export const CHART_X = PADDING_LEFT;
export const CHART_Y = PADDING_TOP;
export const CHART_W = WIDTH - PADDING_LEFT - PADDING_RIGHT; // 1540
export const CHART_H = HEIGHT - PADDING_TOP - PADDING_BOTTOM; // 820

// X-axis: 2015-2025
export const X_MIN = 2015;
export const X_MAX = 2025;
export const X_RANGE = X_MAX - X_MIN; // 10

// Y-axis: 0-20 developer hours
export const Y_MIN = 0;
export const Y_MAX = 20;

// Colors
export const BLUE_LINE_COLOR = "#4A90D9";
export const AMBER_LINE_COLOR = "#D9944A";
export const AXIS_COLOR = "#334155";
export const AXIS_LABEL_COLOR = "#94A3B8";
export const GRID_COLOR = "#334155";
export const GREEN_FORK_COLOR = "#5AAA6E";
export const RED_FORK_COLOR = "#E74C3C";

// Typography
export const FONT_FAMILY = "Inter, sans-serif";
export const MONO_FONT = "'JetBrains Mono', monospace";

// Total duration: 750 frames at 30fps (25s)
export const TOTAL_FRAMES = 750;

// Animation phases
export const CHART_FADE_START = 0;
export const CHART_FADE_END = 30; // Quick 1s re-establishment

export const FORK_START = 60;
export const FORK_DRAW_DURATION = 40;
export const FORK_LOWER_END = 100; // 60 + 40
export const FORK_UPPER_END = 140; // 100 + 40

export const ANNOTATION_SAME_TOOLS_START = 180;
export const ANNOTATION_SAME_TOOLS_FADE = 15;

export const METR_ANNOTATION_START = 240;
export const METR_FADE_DURATION = 15;

export const ACCUMULATION_ARROW_START = 330;
export const ACCUMULATION_ARROW_DRAW = 30;

export const CROSSING_LINE_START = 390;
export const CROSSING_LINE_DRAW = 60;

export const WE_ARE_HERE_START = 480;

export const PROMPT_ANNOTATION_START = 540;
export const TERMINAL_START = 540;

export const HOLD_START = 600;

// Glow pulse cycle
export const GLOW_PULSE_CYCLE = 50; // frames per cycle

// Line widths
export const BLUE_STROKE_WIDTH = 3;
export const AMBER_SOLID_STROKE_WIDTH = 3;
export const AMBER_DASHED_STROKE_WIDTH = 2;
export const FORK_STROKE_WIDTH = 2;

// AI milestones (dimmed further per spec)
export const MILESTONES = [
  { year: 2021, label: "Codex" },
  { year: 2022, label: "Copilot" },
  { year: 2023, label: "GPT-4 / Claude" },
  { year: 2024, label: "Cursor / Claude Code" },
];
export const MILESTONE_OPACITY = 0.06;

// Original triple-line data (from spec 03)
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

// Forked line data
export const SMALL_CODEBASE_DATA = [
  { x: 2020, y: 7 },
  { x: 2022, y: 4 },
  { x: 2024, y: 2 },
  { x: 2025, y: 1 },
];

export const LARGE_CODEBASE_DATA = [
  { x: 2020, y: 7 },
  { x: 2022, y: 10 },
  { x: 2024, y: 11 },
  { x: 2025, y: 12 },
];

// Extended generate line that crosses below both lines
// The blue line continues its descent, crossing dashed total cost (~13h)
// around 2023 and crossing the upper fork (~11h) around 2024
export const GENERATE_CROSSING_DATA = [
  { x: 2015, y: 18 },
  { x: 2018, y: 17.5 },
  { x: 2020, y: 17 },
  { x: 2021, y: 16 },
  { x: 2022, y: 14 },
  { x: 2023, y: 10 },
  { x: 2024, y: 6 },
  { x: 2025, y: 4 },
];

// Helpers to convert data coordinates to pixel coordinates
export function dataToPixelX(year: number): number {
  return CHART_X + ((year - X_MIN) / X_RANGE) * CHART_W;
}

export function dataToPixelY(hours: number): number {
  return CHART_Y + CHART_H * (1 - hours / Y_MAX);
}
