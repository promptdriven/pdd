// Part5Compound06CompoundDebtChart constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0A1628";

// Chart area padding
export const PADDING_LEFT = 200;
export const PADDING_BOTTOM = 200;
export const PADDING_RIGHT = 100;
export const PADDING_TOP = 80;

// Derived chart region
export const CHART_X = PADDING_LEFT; // 200
export const CHART_Y = PADDING_TOP; // 80
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

// Line widths
export const PATCHING_LINE_WIDTH = 4;
export const GENERATION_LINE_WIDTH = 3;

// Animation frames (at 30fps, total 660 frames = 22s)
export const TOTAL_FRAMES = 660;

// Phase 1: Axes fade in (0-30)
export const AXES_FADE_START = 0;
export const AXES_FADE_END = 30;

// Phase 2: Grid lines fade in (20-50)
export const GRID_FADE_START = 20;
export const GRID_FADE_END = 50;

// Phase 3: Curve labels appear at origin (40-45)
export const LABELS_APPEAR_START = 40;
export const LABELS_APPEAR_END = 45;

// Phase 4: Both curves draw simultaneously (45-350)
export const CURVES_DRAW_START = 45;
export const CURVES_DRAW_END = 350;

// Phase 5: Gap fill fades in progressively (100-350)
export const GAP_FILL_START = 100;
export const GAP_FILL_END = 350;

// Phase 6: Gap annotation appears (300-350)
export const ANNOTATION_FADE_START = 300;
export const ANNOTATION_FADE_END = 350;

// Phase 7: Hold (350-600)
// Phase 8: Fade out (600-660)
export const FADEOUT_START = 600;
export const FADEOUT_END = 660;

// Patching curve data (normalized 0-1 on both axes)
export const PATCHING_POINTS = [
  { x: 0, y: 0.02 },
  { x: 0.087, y: 0.06 }, // month 3
  { x: 0.217, y: 0.15 }, // month 6
  { x: 0.348, y: 0.30 }, // month 9
  { x: 0.478, y: 0.50 }, // month 12
  { x: 0.609, y: 0.68 }, // month 15
  { x: 0.739, y: 0.82 }, // month 18
  { x: 0.870, y: 0.91 }, // month 21
  { x: 1.0, y: 0.97 },   // month 24
];

// Generation curve data (normalized, with sawtooth resets)
export const GENERATION_POINTS = [
  { x: 0, y: 0.02 },       // month 1
  { x: 0.130, y: 0.05 },   // month 4 - pre-reset
  { x: 0.174, y: 0.01 },   // month 5 - post-reset
  { x: 0.304, y: 0.05 },   // month 8 - pre-reset
  { x: 0.348, y: 0.01 },   // month 9 - post-reset
  { x: 0.478, y: 0.05 },   // month 12 - pre-reset
  { x: 0.522, y: 0.01 },   // month 13 - post-reset
  { x: 0.652, y: 0.05 },   // month 16 - pre-reset
  { x: 0.696, y: 0.01 },   // month 17 - post-reset
  { x: 0.826, y: 0.05 },   // month 20 - pre-reset
  { x: 0.870, y: 0.01 },   // month 21 - post-reset
  { x: 1.0, y: 0.04 },     // month 24
];

// Grid lines at 25%, 50%, 75%
export const GRID_FRACTIONS = [0.25, 0.5, 0.75];

// Time markers at month 6, 12, 18
export const TIME_MARKERS = [
  { frac: 0.217, label: "Month 6" },
  { frac: 0.478, label: "Month 12" },
  { frac: 0.739, label: "Month 18" },
];
