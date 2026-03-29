// constants.ts — Colors, dimensions, chart data for crossing-lines moment

// ── Canvas ──────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = "#0A0F1A";
export const DURATION_FRAMES = 360;
export const FPS = 30;

// ── Chart Region ────────────────────────────────────────────────────
export const CHART_LEFT = 200;
export const CHART_TOP = 120;
export const CHART_RIGHT = 1720;
export const CHART_BOTTOM = 900;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// ── Axis Labels ─────────────────────────────────────────────────────
export const X_AXIS_YEARS = [2020, 2021, 2022, 2023, 2024, 2025, 2026];
export const Y_AXIS_LABELS = ["$0", "$50", "$100", "$150", "$200"];

// ── Colors ──────────────────────────────────────────────────────────
export const BLUE_LINE_COLOR = "#4A90D9";
export const AMBER_SOLID_COLOR = "#F59E0B";
export const AMBER_DASHED_COLOR = "#D97706";
export const AXIS_COLOR = "#475569";
export const AXIS_LABEL_COLOR = "#94A3B8";
export const GRID_LINE_COLOR = "#1E293B";
export const FLASH_COLOR = "#FFFFFF";
export const LABEL_TEXT_COLOR = "#E2E8F0";
export const LABEL_GLOW_COLOR = "#4A90D9";
export const CONNECTOR_COLOR = "#FFFFFF";

// ── Typography ──────────────────────────────────────────────────────
export const FONT_FAMILY = "Inter, system-ui, sans-serif";
export const TITLE_SIZE = 32;
export const AXIS_LABEL_SIZE = 16;
export const ANNOTATION_SIZE = 24;

// ── Chart Data Points ───────────────────────────────────────────────
// X positions mapped from year to chart pixel space
function yearToX(year: number): number {
  const minYear = 2020;
  const maxYear = 2026;
  return CHART_LEFT + ((year - minYear) / (maxYear - minYear)) * CHART_WIDTH;
}

// Y positions mapped from cost value (0 to 200) to chart pixel space
function costToY(cost: number): number {
  const maxCost = 200;
  return CHART_BOTTOM - (cost / maxCost) * CHART_HEIGHT;
}

export { yearToX, costToY };

// ── Amber line: Total Cost with Debt (dashed) ───────────────────────
// Rises gently over time representing accumulated tech debt cost
export const TOTAL_COST_DEBT_POINTS: Array<[number, number]> = [
  [yearToX(2020), costToY(60)],
  [yearToX(2021), costToY(70)],
  [yearToX(2022), costToY(82)],
  [yearToX(2023), costToY(95)],
  [yearToX(2024), costToY(110)],
  [yearToX(2025), costToY(120)],
  [yearToX(2025.2), costToY(122)],
  [yearToX(2025.6), costToY(125)],
  [yearToX(2026), costToY(130)],
];

// ── Amber line: Immediate Patch Cost (solid) ────────────────────────
// Lower than total debt cost, relatively flat
export const IMMEDIATE_PATCH_POINTS: Array<[number, number]> = [
  [yearToX(2020), costToY(40)],
  [yearToX(2021), costToY(42)],
  [yearToX(2022), costToY(46)],
  [yearToX(2023), costToY(50)],
  [yearToX(2024), costToY(55)],
  [yearToX(2025), costToY(58)],
  [yearToX(2025.2), costToY(59)],
  [yearToX(2025.6), costToY(60)],
  [yearToX(2026), costToY(62)],
];

// ── Blue line: Cost to Generate ─────────────────────────────────────
// Starts high, plunges through both amber lines around 2025.2 and 2025.6
export const GENERATE_COST_POINTS: Array<[number, number]> = [
  [yearToX(2020), costToY(180)],
  [yearToX(2021), costToY(170)],
  [yearToX(2022), costToY(155)],
  [yearToX(2023), costToY(135)],
  [yearToX(2024), costToY(105)],
  [yearToX(2025), costToY(80)],
  [yearToX(2025.2), costToY(60)],  // ← crosses total cost debt here (≈122 on debt line, but generate is now cheaper)
];

// The "pre-crossing" portion: frames 0-60 show the line up to ~2025
export const GENERATE_VISIBLE_BEFORE_INDEX = 6; // up to yearToX(2025), costToY(80)

// Final descent data — the blue line continues past the crossings
export const GENERATE_DESCENT_POINTS: Array<[number, number]> = [
  [yearToX(2025), costToY(80)],
  [yearToX(2025.2), costToY(60)],   // crosses total cost debt
  [yearToX(2025.6), costToY(35)],   // crosses immediate patch
  [yearToX(2026), costToY(18)],     // well below both
];

// ── Crossing Points (pixel coordinates) ─────────────────────────────
// Crossing 1: generate crosses total_cost_debt around year 2025.2
export const CROSSING_1_X = yearToX(2025.2);
export const CROSSING_1_Y = costToY(122); // the debt line value at that year

// Crossing 2: generate crosses immediate_patch around year 2025.6
export const CROSSING_2_X = yearToX(2025.6);
export const CROSSING_2_Y = costToY(60); // the patch line value at that year

// ── "We are here" label position ────────────────────────────────────
export const LABEL_X = CROSSING_2_X + 40;
export const LABEL_Y = CROSSING_2_Y + 50;

// ── Animation Timing (frames) ───────────────────────────────────────
export const PHASE_ESTABLISH_END = 60;
export const PHASE_FIRST_CROSSING_START = 60;
export const PHASE_FIRST_CROSSING_END = 120;
export const PHASE_SECOND_CROSSING_START = 120;
export const PHASE_SECOND_CROSSING_END = 180;
export const PHASE_LABEL_START = 180;
export const PHASE_LABEL_FADE_DURATION = 30;
export const PHASE_HOLD_START = 240;

// Flash timing relative to sequence
export const FLASH_1_FRAME = 90;  // midway through first crossing
export const FLASH_2_FRAME = 150; // midway through second crossing
export const FLASH_DURATION = 20;

// Label pulse
export const LABEL_PULSE_PERIOD = 60;
