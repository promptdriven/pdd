// ── Colors ──────────────────────────────────────────────────────────────────
export const BG_COLOR = '#0F172A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.06;
export const AMBER = '#D9944A';
export const BLUE = '#4A90D9';
export const CROSSING_COLOR = '#E2E8F0';
export const CROSSING_GLOW_OPACITY = 0.2;
export const GREEN_ZONE = '#22C55E';
export const RED_ZONE = '#EF4444';
export const AXIS_LABEL_COLOR = '#64748B';
export const NEEDLE_COLOR = '#94A3B8';
export const STRIKETHROUGH_COLOR = '#EF4444';

// ── Dimensions ──────────────────────────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const CHART_LEFT = 160;
export const CHART_RIGHT = 1760;
export const CHART_TOP = 100;
export const CHART_BOTTOM = 900;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// ── Timing (frames) ────────────────────────────────────────────────────────
export const FPS = 30;
export const TOTAL_FRAMES = 300;

export const FADE_IN_END = 30;
export const PULSE_START = 30;
export const MORPH_START = 60;
export const MORPH_END = 150;
export const MORPH_DURATION = MORPH_END - MORPH_START; // 90 frames
export const RELABEL_START = 150;
export const RELABEL_END = 210;
export const NEEDLE_START = 210;
export const NEEDLE_SCALE_DURATION = 15;
export const STRIKETHROUGH_START = 220;
export const STRIKETHROUGH_DURATION = 10;

// ── Crossing point ─────────────────────────────────────────────────────────
export const CROSSING_RADIUS = 14;
export const CROSSING_GLOW_RADIUS = 24;
export const PULSE_CYCLE = 30;
export const PULSE_SCALE_MIN = 1.0;
export const PULSE_SCALE_MAX = 1.3;

// ── Chart Data (initial — sock economics) ──────────────────────────────────
export const INITIAL_X_LABELS = ['1950', '1960', '1970', '1980', '1990', '2000', '2010', '2020'];
export const FINAL_X_LABELS = ['2020', '2022', '2024', '2026', '2028', '2030', '', ''];

export const Y_MAX = 30;
export const Y_STEP = 10; // grid lines at $10 intervals

// Labor cost: rises from $2 (1950) to $25 (2020)
export const LABOR_COST_DATA: [number, number][] = [
  [1950, 2], [1955, 3], [1960, 4.5], [1965, 6], [1970, 8],
  [1975, 10], [1980, 12], [1985, 14], [1990, 16], [1995, 18],
  [2000, 20], [2005, 21.5], [2010, 23], [2015, 24], [2020, 25],
];

// Sock cost: falls from $8 (1950) to $0.50 (2020)
export const SOCK_COST_DATA: [number, number][] = [
  [1950, 8], [1955, 7], [1960, 5.5], [1965, 4], [1970, 3.2],
  [1975, 2.6], [1980, 2.2], [1985, 1.8], [1990, 1.5], [1995, 1.2],
  [2000, 1.0], [2005, 0.8], [2010, 0.7], [2015, 0.6], [2020, 0.5],
];

// Patching cost (post-morph): rises from $5 (2020) to $28 (2030)
export const PATCHING_COST_DATA: [number, number][] = [
  [2020, 5], [2021, 7], [2022, 10], [2023, 13], [2024, 16],
  [2025, 19], [2026, 21], [2027, 23], [2028, 25], [2029, 27], [2030, 28],
];

// Generation cost (post-morph): falls from $22 (2020) to $1 (2030)
export const GENERATION_COST_DATA: [number, number][] = [
  [2020, 22], [2021, 18], [2022, 14], [2023, 11], [2024, 8],
  [2025, 5.5], [2026, 4], [2027, 3], [2028, 2], [2029, 1.5], [2030, 1],
];

// Crossing positions (normalized 0-1 along chart width)
// 1962 within 1950-2020: (1962-1950)/(2020-1950) ≈ 0.171
export const INITIAL_CROSSING_X_NORM = (1962 - 1950) / (2020 - 1950);
// Crossing Y: ~$5 (labor meets sock around 1962 at ~$5)
export const INITIAL_CROSSING_Y_NORM = 5 / Y_MAX;

// 2024 within 2020-2030: (2024-2020)/(2030-2020) = 0.4
export const FINAL_CROSSING_X_NORM = (2024 - 2020) / (2030 - 2020);
// Crossing Y at 2024: patching ~$16, generation ~$8 → meet around ~$12
export const FINAL_CROSSING_Y_NORM = 12 / Y_MAX;

// ── Label strings ──────────────────────────────────────────────────────────
export const INITIAL_LINE1_LABEL = 'Labor cost (per hour)';
export const FINAL_LINE1_LABEL = 'Patching cost (per fix)';
export const INITIAL_LINE2_LABEL = 'Sock cost';
export const FINAL_LINE2_LABEL = 'Generation cost';
export const INITIAL_CROSSING_LABEL = 'The Threshold';
export const FINAL_CROSSING_LABEL = 'Now';
export const INITIAL_POST_LABEL = 'Darning irrational';
export const FINAL_POST_LABEL = 'Patching irrational';

// ── Needle position ────────────────────────────────────────────────────────
export const NEEDLE_X = 1400;
export const NEEDLE_Y = 600;
