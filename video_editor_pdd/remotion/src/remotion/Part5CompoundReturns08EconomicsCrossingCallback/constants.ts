// === Colors ===
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.08;

export const GENERATE_LINE_COLOR = '#4A90D9';
export const PATCH_LINE_COLOR = '#D9944A';
export const DEBT_AREA_COLOR = '#D9944A';
export const DEBT_AREA_OPACITY = 0.12;

export const LABEL_COLOR = '#E2E8F0';
export const LABEL_DIMMED_OPACITY = 0.4;
export const DATE_MARKER_COLOR = '#64748B';
export const DATE_MARKER_OPACITY = 0.3;

export const PULSE_GLOW_COLOR = '#FFFFFF';
export const PULSE_MIN_OPACITY = 0.05;
export const PULSE_MAX_OPACITY = 0.2;
export const PULSE_RADIUS = 25;

export const REFRAME_UNDERLINE_COLOR = '#4A90D9';
export const REFRAME_UNDERLINE_OPACITY = 0.1;

// === Dimensions ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// Chart area
export const CHART_LEFT = 160;
export const CHART_RIGHT = 1760;
export const CHART_TOP = 100;
export const CHART_BOTTOM = 780;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// === Line widths ===
export const GENERATE_LINE_WIDTH = 3;
export const PATCH_LINE_WIDTH = 3;
export const DEBT_LINE_WIDTH = 2.5;

// === Timeline ===
export const TOTAL_FRAMES = 300;
export const FPS = 30;

// Animation phases
export const CHART_FADE_IN_START = 0;
export const CHART_FADE_IN_END = 30;
export const PULSE_START = 30;
export const LABEL_REEMPHASIZE_START = 90;
export const REFRAME_TEXT_START = 150;
export const REFRAME_TEXT_END = 180;
export const CHART_FADE_OUT_START = 270;
export const CHART_FADE_OUT_END = 300;
export const PULSE_CYCLE_FRAMES = 30;

// === Chart data points (years) ===
export const YEAR_START = 2020;
export const YEAR_END = 2027;

// Crossing point position (where blue crosses below amber solid)
export const CROSSING_YEAR = 2025.6;

// Cost lines data: [year, cost] tuples (normalized 0-1 range)
export const GENERATE_LINE_DATA: [number, number][] = [
  [2020, 0.95],
  [2021, 0.88],
  [2022, 0.72],
  [2023, 0.55],
  [2024, 0.38],
  [2025, 0.28],
  [2025.6, 0.22],
  [2026, 0.16],
  [2027, 0.1],
];

export const PATCH_LINE_DATA: [number, number][] = [
  [2020, 0.2],
  [2021, 0.22],
  [2022, 0.24],
  [2023, 0.25],
  [2024, 0.24],
  [2025, 0.23],
  [2025.6, 0.22],
  [2026, 0.22],
  [2027, 0.21],
];

export const DEBT_LINE_DATA: [number, number][] = [
  [2020, 0.25],
  [2021, 0.32],
  [2022, 0.42],
  [2023, 0.52],
  [2024, 0.6],
  [2025, 0.68],
  [2025.6, 0.72],
  [2026, 0.76],
  [2027, 0.82],
];

// Helper: convert year/cost to pixel coords
export function yearToX(year: number): number {
  const t = (year - YEAR_START) / (YEAR_END - YEAR_START);
  return CHART_LEFT + t * CHART_WIDTH;
}

export function costToY(cost: number): number {
  return CHART_TOP + (1 - cost) * CHART_HEIGHT;
}

// Crossing point pixel position
export const CROSSING_X = yearToX(CROSSING_YEAR);
export const CROSSING_Y = costToY(0.22);

// Grid horizontal lines (every 150px from top)
export const GRID_LINES_Y: number[] = [];
for (let y = CHART_TOP; y <= CHART_BOTTOM; y += 150) {
  GRID_LINES_Y.push(y);
}

// Year markers
export const YEAR_MARKERS = [2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027];
