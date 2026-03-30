// constants.ts — Colors, dimensions, and chart data for Section 1.13: The Crossing Lines Moment

// ─── Canvas ───
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = '#0A0F1A';
export const DURATION_FRAMES = 360;
export const FPS = 30;

// ─── Chart Layout ───
export const CHART_PADDING_LEFT = 180;
export const CHART_PADDING_RIGHT = 120;
export const CHART_PADDING_TOP = 100;
export const CHART_PADDING_BOTTOM = 120;
export const CHART_LEFT = CHART_PADDING_LEFT;
export const CHART_RIGHT = CANVAS_WIDTH - CHART_PADDING_RIGHT;
export const CHART_TOP = CHART_PADDING_TOP;
export const CHART_BOTTOM = CANVAS_HEIGHT - CHART_PADDING_BOTTOM;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// ─── Axis Ranges ───
export const YEAR_MIN = 2020;
export const YEAR_MAX = 2026;
export const COST_MIN = 0;
export const COST_MAX = 100; // arbitrary units for relative cost

// ─── Colors ───
export const LINE_GENERATE_COLOR = '#4A90D9';
export const LINE_TOTAL_COST_COLOR = '#F59E0B'; // amber dashed
export const LINE_IMMEDIATE_PATCH_COLOR = '#F59E0B'; // amber solid
export const CROSSING_FLASH_COLOR = '#FFFFFF';
export const LABEL_TEXT_COLOR = '#E2E8F0';
export const LABEL_GLOW_COLOR = '#4A90D9';
export const AXIS_COLOR = '#475569';
export const AXIS_LABEL_COLOR = '#94A3B8';
export const GRID_COLOR = '#1E293B';
export const CONNECTOR_COLOR = '#FFFFFF';

// ─── Typography ───
export const FONT_FAMILY = 'Inter, system-ui, sans-serif';
export const LABEL_FONT_SIZE = 24;
export const LABEL_FONT_WEIGHT = 700;
export const AXIS_FONT_SIZE = 14;
export const TITLE_FONT_SIZE = 20;

// ─── Animation Timing (frames) ───
export const PHASE_ESTABLISH_START = 0;
export const PHASE_ESTABLISH_END = 60;
export const PHASE_CROSS1_START = 60;
export const PHASE_CROSS1_END = 120;
export const PHASE_CROSS2_START = 120;
export const PHASE_CROSS2_END = 180;
export const PHASE_LABEL_START = 180;
export const PHASE_LABEL_END = 210; // 30 frames fade-in
export const PHASE_HOLD_START = 240;
export const PHASE_HOLD_END = 360;
export const FLASH1_FRAME = 100; // near end of crossing 1
export const FLASH2_FRAME = 155; // near end of crossing 2
export const FLASH_DURATION = 20;

// ─── Chart Data Points ───
// Cost to generate (blue) — starts high, plunges
export const GENERATE_LINE_POINTS: Array<{ year: number; cost: number }> = [
  { year: 2020, cost: 95 },
  { year: 2021, cost: 88 },
  { year: 2022, cost: 75 },
  { year: 2023, cost: 58 },
  { year: 2024, cost: 40 },
  { year: 2024.8, cost: 28 },
  { year: 2025.2, cost: 18 }, // crosses total cost here
  { year: 2025.6, cost: 10 }, // crosses immediate patch here
  { year: 2026, cost: 5 },
];

// Total cost with debt (amber dashed) — relatively flat/slight increase
export const TOTAL_COST_LINE_POINTS: Array<{ year: number; cost: number }> = [
  { year: 2020, cost: 15 },
  { year: 2021, cost: 16 },
  { year: 2022, cost: 17 },
  { year: 2023, cost: 18 },
  { year: 2024, cost: 19 },
  { year: 2025, cost: 20 },
  { year: 2025.2, cost: 18 }, // crossing point
  { year: 2026, cost: 22 },
];

// Immediate patch cost (amber solid) — lower baseline
export const IMMEDIATE_PATCH_LINE_POINTS: Array<{ year: number; cost: number }> = [
  { year: 2020, cost: 8 },
  { year: 2021, cost: 9 },
  { year: 2022, cost: 9.5 },
  { year: 2023, cost: 10 },
  { year: 2024, cost: 10.5 },
  { year: 2025, cost: 11 },
  { year: 2025.6, cost: 10 }, // crossing point
  { year: 2026, cost: 12 },
];

// ─── Crossing Coordinates (in chart space) ───
export const CROSSING_1_YEAR = 2025.2;
export const CROSSING_1_COST = 18;
export const CROSSING_2_YEAR = 2025.6;
export const CROSSING_2_COST = 10;

// ─── Helper: Convert data coords to pixel coords ───
export function yearToX(year: number): number {
  return CHART_LEFT + ((year - YEAR_MIN) / (YEAR_MAX - YEAR_MIN)) * CHART_WIDTH;
}

export function costToY(cost: number): number {
  return CHART_BOTTOM - ((cost - COST_MIN) / (COST_MAX - COST_MIN)) * CHART_HEIGHT;
}

// Pixel positions of crossings
export const CROSSING_1_X = yearToX(CROSSING_1_YEAR);
export const CROSSING_1_Y = costToY(CROSSING_1_COST);
export const CROSSING_2_X = yearToX(CROSSING_2_YEAR);
export const CROSSING_2_Y = costToY(CROSSING_2_COST);

// ─── Y-Axis Labels ───
export const Y_AXIS_TICKS = [0, 20, 40, 60, 80, 100];
export const X_AXIS_TICKS = [2020, 2021, 2022, 2023, 2024, 2025, 2026];

// ─── Legend ───
export const LEGEND_ITEMS = [
  { label: 'Cost to Generate', color: LINE_GENERATE_COLOR, dashed: false },
  { label: 'Total Cost (incl. debt)', color: LINE_TOTAL_COST_COLOR, dashed: true },
  { label: 'Immediate Patch Cost', color: LINE_IMMEDIATE_PATCH_COLOR, dashed: false },
];
