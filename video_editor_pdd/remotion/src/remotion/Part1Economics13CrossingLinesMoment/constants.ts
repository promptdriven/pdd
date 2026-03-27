// ── Colors ──────────────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const BLUE_LINE_COLOR = "#4A90D9";
export const AMBER_SOLID_COLOR = "#D97706";
export const AMBER_DASHED_COLOR = "#F59E0B";
export const LABEL_TEXT_COLOR = "#E2E8F0";
export const LABEL_GLOW_COLOR = "#4A90D9";
export const FLASH_COLOR = "#FFFFFF";
export const AXIS_COLOR = "#475569";
export const AXIS_LABEL_COLOR = "#94A3B8";
export const GRID_LINE_COLOR = "#1E293B";
export const CONNECTOR_COLOR = "#FFFFFF";

// ── Dimensions ──────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// Chart area (padded within canvas)
export const CHART_LEFT = 160;
export const CHART_RIGHT = 1760;
export const CHART_TOP = 100;
export const CHART_BOTTOM = 900;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// ── Timing (frames @ 30fps) ────────────────────────────────────────
export const TOTAL_FRAMES = 360;
export const FPS = 30;

export const PHASE_ESTABLISH_START = 0;
export const PHASE_ESTABLISH_END = 60;

export const PHASE_CROSS1_START = 60;
export const PHASE_CROSS1_END = 120;

export const PHASE_CROSS2_START = 120;
export const PHASE_CROSS2_END = 180;

export const PHASE_LABEL_START = 180;
export const PHASE_LABEL_END = 210; // fade-in over 30 frames

export const PHASE_HOLD_START = 240;
export const PHASE_HOLD_END = 360;

export const FLASH1_FRAME = 105; // mid crossing-1
export const FLASH2_FRAME = 150; // mid crossing-2

// ── Chart data ──────────────────────────────────────────────────────
// X-axis: years 2020 → 2026
export const X_MIN_YEAR = 2020;
export const X_MAX_YEAR = 2026;

// Y-axis: relative cost (0 → 100, arbitrary units)
export const Y_MIN = 0;
export const Y_MAX = 100;

// Amber lines (flat/slowly rising horizontal reference lines)
// "Total cost with debt" — dashed — higher line
export const TOTAL_COST_DEBT_Y = 55;
// "Immediate patch cost" — solid — lower line
export const IMMEDIATE_PATCH_Y = 40;

// Blue "generate" line key-points (year, cost)
export const GENERATE_LINE_POINTS: [number, number][] = [
  [2020, 95],
  [2021, 90],
  [2022, 82],
  [2023, 70],
  [2024, 60],
  [2024.8, 52],
  [2025.2, 42], // crosses total_cost_debt (~55→42 but crossing is at 55)
  [2025.6, 28], // crosses immediate_patch (~40→28 but crossing is at 40)
  [2026, 15],
];

// Crossing point coordinates (in chart-data space)
export const CROSSING1_YEAR = 2025.0;
export const CROSSING1_Y = TOTAL_COST_DEBT_Y; // where generate = total_cost_debt

export const CROSSING2_YEAR = 2025.4;
export const CROSSING2_Y = IMMEDIATE_PATCH_Y; // where generate = immediate_patch

// ── Typography ──────────────────────────────────────────────────────
export const FONT_FAMILY = "Inter, system-ui, sans-serif";
export const LABEL_FONT_SIZE = 24;
export const LABEL_FONT_WEIGHT = 700;
export const AXIS_FONT_SIZE = 14;
export const LEGEND_FONT_SIZE = 16;

// ── Misc ────────────────────────────────────────────────────────────
export const FLASH1_RADIUS = 20;
export const FLASH2_RADIUS = 15;
export const CONNECTOR_OPACITY = 0.3;
export const LABEL_GLOW_OPACITY = 0.1;
export const BLUE_LINE_STROKE_WIDTH = 3;
export const AMBER_LINE_STROKE_WIDTH = 2;
