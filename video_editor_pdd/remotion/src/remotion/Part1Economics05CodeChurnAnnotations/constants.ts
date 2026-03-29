// ── Canvas ──────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = "#0A0F1A";
export const TOTAL_FRAMES = 840;
export const FPS = 30;

// ── Palette ─────────────────────────────────────────────────────
export const COLOR_RED_ACCENT = "#EF4444";
export const COLOR_AMBER_ACCENT = "#F59E0B";
export const COLOR_CALLOUT_FILL = "#1E293B";
export const COLOR_SOURCE_TEXT = "#94A3B8";
export const COLOR_CHART_SOLID = "#F59E0B";
export const COLOR_CHART_DASHED = "#F59E0B";
export const COLOR_CHART_DEBT_FILL = "#F59E0B";
export const COLOR_AXIS_LABEL = "#64748B";
export const COLOR_AXIS_LINE = "#334155";
export const COLOR_PREV_ANNOTATION_BORDER = "#3B82F6";
export const COLOR_WHITE = "#FFFFFF";

// ── Chart Layout (inside the 1920×1080 canvas) ─────────────────
export const CHART_LEFT = 140;
export const CHART_TOP = 120;
export const CHART_WIDTH = 1100;
export const CHART_HEIGHT = 600;
export const CHART_BOTTOM = CHART_TOP + CHART_HEIGHT; // 720

// X-axis years
export const YEAR_START = 2019;
export const YEAR_END = 2025;

// ── Chart data (normalised 0-1 range for Y) ─────────────────────
// "Solid line" = total code generation cost (rises)
export const SOLID_LINE_POINTS: [number, number][] = [
  [2019, 0.18],
  [2020, 0.22],
  [2021, 0.30],
  [2022, 0.38],
  [2023, 0.55],
  [2024, 0.75],
  [2025, 0.90],
];

// "Dashed line" = maintainable / patched cost (lower, creating the gap)
export const DASHED_LINE_POINTS: [number, number][] = [
  [2019, 0.16],
  [2020, 0.19],
  [2021, 0.24],
  [2022, 0.28],
  [2023, 0.30],
  [2024, 0.32],
  [2025, 0.34],
];

// ── Annotation positions (pixel coords) ─────────────────────────
export const ANNOTATION1_X = 1340;
export const ANNOTATION1_Y = 340;
export const ANNOTATION2_X = 1340;
export const ANNOTATION2_Y = 500;

export const CALLOUT_WIDTH = 340;
export const CALLOUT_HEIGHT_SINGLE = 72;
export const CALLOUT_BORDER_RADIUS = 8;
export const CALLOUT_BORDER_WIDTH = 1.5;

// ── Previous annotations (GitHub / Uplevel) placeholders ────────
export const PREV_ANNOTATION_1_POS = { x: 1320, y: 200 };
export const PREV_ANNOTATION_2_POS = { x: 1320, y: 280 };

// ── Animation timing (frames) ───────────────────────────────────
export const PREV_FADE_START = 0;
export const PREV_FADE_END = 60;

export const ANN1_APPEAR = 60;
export const ANN1_CONNECTOR_DUR = 30;
export const ANN1_SCALE_DUR = 20;

export const ANN2_APPEAR = 360;
export const ANN2_CONNECTOR_DUR = 30;
export const ANN2_SCALE_DUR = 20;

export const DEBT_PULSE_START = 60;
export const DEBT_PULSE_CYCLE = 45;
export const DEBT_PULSE_MIN = 0.12;
export const DEBT_PULSE_MAX = 0.20;

// ── Typography ──────────────────────────────────────────────────
export const FONT_MAIN_SIZE = 18;
export const FONT_SOURCE_SIZE = 12;
export const FONT_WEIGHT_BOLD = 700;
export const FONT_WEIGHT_REGULAR = 400;
