// Part1Economics04ResearchAnnotations constants
// Continues the triple-line chart from spec 03 with research annotation overlays.

// ── Canvas ────────────────────────────────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0D1117";

// ── Chart area (identical to spec 03) ─────────────────────────────────────────
export const PADDING_LEFT = 280;
export const PADDING_RIGHT = 100;
export const PADDING_TOP = 140;
export const PADDING_BOTTOM = 120;

export const CHART_X = PADDING_LEFT;
export const CHART_Y = PADDING_TOP;
export const CHART_W = WIDTH - PADDING_LEFT - PADDING_RIGHT; // 1540
export const CHART_H = HEIGHT - PADDING_TOP - PADDING_BOTTOM; // 820

export const X_MIN = 2015;
export const X_MAX = 2025;
export const X_RANGE = X_MAX - X_MIN;

export const Y_MIN = 0;
export const Y_MAX = 20;

// ── Helpers (defined early so constants below can use them) ───────────────────
export function dataToPixelX(year: number): number {
  return CHART_X + ((year - X_MIN) / X_RANGE) * CHART_W;
}

export function dataToPixelY(hours: number): number {
  return CHART_Y + CHART_H * (1 - hours / Y_MAX);
}

// ── Colors ────────────────────────────────────────────────────────────────────
export const BLUE_LINE_COLOR = "#4A90D9";
export const AMBER_LINE_COLOR = "#D9944A";
export const RED_COLOR = "#E74C3C";
export const AXIS_COLOR = "#334155";
export const AXIS_LABEL_COLOR = "#94A3B8";
export const GRID_COLOR = "#334155";
export const CALLOUT_BG = "#1A2332";

// ── Typography ────────────────────────────────────────────────────────────────
export const FONT_FAMILY = "Inter, sans-serif";

// ── Line widths ───────────────────────────────────────────────────────────────
export const BLUE_STROKE_WIDTH = 3;
export const AMBER_SOLID_STROKE_WIDTH = 3;
export const AMBER_DASHED_STROKE_WIDTH = 2;

// ── Chart data (replicated from spec 03, chart is fully drawn from frame 0) ──
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

export const MILESTONES = [
  { year: 2021, label: "Codex" },
  { year: 2022, label: "Copilot" },
  { year: 2023, label: "GPT-4 / Claude" },
  { year: 2024, label: "Cursor / Claude Code" },
];

// ── Debt area ─────────────────────────────────────────────────────────────────
export const DEBT_OPACITY = 0.10;
export const DEBT_PULSE_CYCLE = 60;
export const DEBT_OPACITY_MIN = 0.08;
export const DEBT_OPACITY_MAX = 0.12;

// ── Animation frames (30fps, 900 total) ───────────────────────────────────────
export const TOTAL_FRAMES = 900;

// Phase 1: Chart holds (from previous spec, fully drawn)
export const HOLD_START = 0;
export const HOLD_END = 30;

// Phase 2: Annotation 1 — GitHub study (frame 30-120)
export const ANN1_START = 30;
export const ANN1_FADE_DUR = 20;

// Phase 3: Annotation 2 — Uplevel study (frame 120-210)
export const ANN2_START = 120;
export const ANN2_FADE_DUR = 20;

// Phase 4: Brief hold (210-240)

// Phase 5: Annotation 3 — GitClear data (frame 240-360)
export const ANN3_START = 240;
export const ANN3_FADE_DUR = 20;

// Phase 6: Hold for narration (360-540)

// Phase 7: Debt layer decomposition (frame 540-660)
export const DEBT_SPLIT_START = 540;
export const DEBT_SPLIT_DUR = 30;

// Phase 8: Hold with noise animation (660-900)

// ── Annotation positions ──────────────────────────────────────────────────────
// Callout boxes positioned on the right side of the chart

// Annotation 1: Points to solid amber line at ~2022
export const ANN1_BOX_X = 1360;
export const ANN1_BOX_Y = 250;
export const ANN1_TARGET_X = dataToPixelX(2022);
export const ANN1_TARGET_Y = dataToPixelY(5); // patch cost at 2022

// Annotation 2: Points to dashed amber line at ~2024
export const ANN2_BOX_X = 1360;
export const ANN2_BOX_Y = 400;
export const ANN2_TARGET_X = dataToPixelX(2024);
export const ANN2_TARGET_Y = dataToPixelY(13); // total cost at 2024

// Annotation 3: Points to debt shaded area
export const ANN3_BOX_X = 1360;
export const ANN3_BOX_Y = 580;
export const ANN3_TARGET_X = dataToPixelX(2023.5);
export const ANN3_TARGET_Y = dataToPixelY(8.5); // center of debt area

// ── Connection line draw duration ─────────────────────────────────────────────
export const CONNECTION_DRAW_DUR = 15;
