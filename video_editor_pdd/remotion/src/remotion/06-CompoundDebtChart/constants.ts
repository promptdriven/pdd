// Part5Compound06CompoundDebtChart constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;

// Chart area padding (spec: 200px left/bottom, 100px right/top)
export const PADDING_LEFT = 200;
export const PADDING_BOTTOM = 200;
export const PADDING_RIGHT = 100;
export const PADDING_TOP = 80;

// Derived chart region: (200, 80) to (1820, 880)
export const CHART_X = PADDING_LEFT;
export const CHART_Y = PADDING_TOP;
export const CHART_W = WIDTH - PADDING_LEFT - PADDING_RIGHT; // 1620
export const CHART_H = HEIGHT - PADDING_TOP - PADDING_BOTTOM; // 800

// Colors
export const PATCHING_COLOR = "#EF4444";
export const GENERATION_COLOR = "#22C55E";
export const AXIS_COLOR = "#94A3B8";
export const AXIS_TITLE_COLOR = "#CBD5E1";
export const GRID_COLOR = "#334155";
export const TIME_MARKER_COLOR = "#64748B";
export const ANNOTATION_COLOR = "#FFFFFF";
export const GAP_FILL_COLOR_START = "rgba(239, 68, 68, 0.04)";
export const GAP_FILL_COLOR_END = "rgba(239, 68, 68, 0.15)";

// Line widths
export const PATCHING_LINE_WIDTH = 4;
export const GENERATION_LINE_WIDTH = 3;

// Grid fractions for horizontal reference lines
export const GRID_FRACTIONS = [0.25, 0.5, 0.75];

// Time marker positions (normalized 0-1) — Month 6, 12, 18
export const TIME_MARKERS = [
  { frac: (6 - 1) / 23, label: "Month 6" },
  { frac: (12 - 1) / 23, label: "Month 12" },
  { frac: (18 - 1) / 23, label: "Month 18" },
];

// Typography
export const FONT_FAMILY = "Inter, sans-serif";

// Animation frames (at 30fps, total 660 frames = 22s)
export const TOTAL_FRAMES = 660;

// Phase 1: Axes fade in (0-30)
export const AXES_FADE_START = 0;
export const AXES_FADE_END = 30;

// Phase 2: Grid + time markers fade in (20-50)
export const GRID_FADE_START = 20;
export const GRID_FADE_END = 50;

// Phase 3: Curve labels appear (40-45)
export const LABELS_APPEAR_START = 40;
export const LABELS_APPEAR_END = 45;

// Phase 4: Curves draw (45-350)
export const CURVES_DRAW_START = 45;
export const CURVES_DRAW_END = 350;

// Phase 5: Gap fill fades in (100-350)
export const GAP_FILL_START = 100;
export const GAP_FILL_END = 350;

// Phase 6: Annotation appears (300-350)
export const ANNOTATION_FADE_START = 300;
export const ANNOTATION_FADE_END = 350;

// Phase 7: Hold (350-600) — nothing changes

// Phase 8: Fade out (600-660)
export const FADEOUT_START = 600;
export const FADEOUT_END = 660;

// Patching curve data (normalized 0-1, exponential climb)
// x: month fraction (month-1)/23, y: debt level 0-1
export const PATCHING_POINTS = [
  { x: 0 / 23, y: 0.02 },
  { x: 2 / 23, y: 0.06 },
  { x: 5 / 23, y: 0.15 },
  { x: 8 / 23, y: 0.30 },
  { x: 11 / 23, y: 0.50 },
  { x: 14 / 23, y: 0.68 },
  { x: 17 / 23, y: 0.82 },
  { x: 20 / 23, y: 0.91 },
  { x: 23 / 23, y: 0.97 },
];

// Generation curve data (flat with sawtooth resets)
// x: month fraction, y: debt level 0-1
export const GENERATION_POINTS = [
  { x: 0 / 23, y: 0.02 },
  { x: 3 / 23, y: 0.05 }, // pre-reset peak
  { x: 4 / 23, y: 0.01 }, // post-reset
  { x: 7 / 23, y: 0.05 }, // pre-reset peak
  { x: 8 / 23, y: 0.01 }, // post-reset
  { x: 11 / 23, y: 0.05 }, // pre-reset peak
  { x: 12 / 23, y: 0.01 }, // post-reset
  { x: 15 / 23, y: 0.05 }, // pre-reset peak
  { x: 16 / 23, y: 0.01 }, // post-reset
  { x: 19 / 23, y: 0.05 }, // pre-reset peak
  { x: 20 / 23, y: 0.01 }, // post-reset
  { x: 23 / 23, y: 0.04 },
];

// Gap annotation position
export const ANNOTATION_X = 1200;
export const ANNOTATION_Y = 400;
