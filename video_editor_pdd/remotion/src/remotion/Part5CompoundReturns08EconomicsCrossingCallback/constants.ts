// ── Canvas ──────────────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BG_COLOR = "#0A0F1A";

// ── Grid ────────────────────────────────────────────────────────────────────
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.08;
export const GRID_INTERVAL = 150; // px between horizontal lines

// ── Chart area ──────────────────────────────────────────────────────────────
export const CHART_LEFT = 160;
export const CHART_TOP = 100;
export const CHART_WIDTH = 1600;
export const CHART_HEIGHT = 650;

// ── Line colors & widths ────────────────────────────────────────────────────
export const GENERATE_COLOR = "#4A90D9";
export const GENERATE_WIDTH = 3;

export const PATCH_COLOR = "#D9944A";
export const PATCH_SOLID_WIDTH = 3;
export const PATCH_DASHED_WIDTH = 2.5;

export const DEBT_AREA_COLOR = "#D9944A";
export const DEBT_AREA_OPACITY = 0.12;

// ── Crossing point ─────────────────────────────────────────────────────────
export const CROSSING_YEAR = 2025.6;
export const CROSSING_GLOW_COLOR = "#FFFFFF";
export const CROSSING_GLOW_RADIUS = 25;
export const CROSSING_GLOW_MIN_OPACITY = 0.05;
export const CROSSING_GLOW_MAX_OPACITY = 0.2;
export const CROSSING_PULSE_CYCLE = 30; // frames per pulse cycle

// ── Text styling ────────────────────────────────────────────────────────────
export const LABEL_COLOR = "#E2E8F0";
export const LABEL_DIMMED_OPACITY = 0.62;
export const WE_ARE_HERE_OPACITY = 0.78;
export const ACCENT_UNDERLINE_COLOR = "#4A90D9";
export const ACCENT_UNDERLINE_OPACITY = 0.7;

export const DATE_MARKER_COLOR = "#64748B";
export const DATE_MARKER_OPACITY = 0.62;

// ── Chart data (years ~ 2020–2027) ─────────────────────────────────────────
export const CHART_MIN_YEAR = 2020;
export const CHART_MAX_YEAR = 2027;
export const CHART_MIN_COST = 0;
export const CHART_MAX_COST = 100;

// Generate line (blue) — starts high, drops steeply then flattens well below patch
export const GENERATE_POINTS: { x: number; y: number }[] = [
  { x: 2020, y: 85 },
  { x: 2021, y: 78 },
  { x: 2022, y: 65 },
  { x: 2023, y: 50 },
  { x: 2024, y: 38 },
  { x: 2025, y: 28 },
  { x: 2025.6, y: 24 },
  { x: 2026, y: 18 },
  { x: 2027, y: 12 },
];

// Immediate patch line (amber solid) — stays moderate, slowly rises
export const PATCH_POINTS: { x: number; y: number }[] = [
  { x: 2020, y: 20 },
  { x: 2021, y: 22 },
  { x: 2022, y: 24 },
  { x: 2023, y: 25 },
  { x: 2024, y: 26 },
  { x: 2025, y: 27 },
  { x: 2025.6, y: 28 },
  { x: 2026, y: 30 },
  { x: 2027, y: 32 },
];

// Total cost with debt line (amber dashed) — higher, climbing steadily
export const DEBT_POINTS: { x: number; y: number }[] = [
  { x: 2020, y: 30 },
  { x: 2021, y: 36 },
  { x: 2022, y: 42 },
  { x: 2023, y: 50 },
  { x: 2024, y: 58 },
  { x: 2025, y: 65 },
  { x: 2025.6, y: 68 },
  { x: 2026, y: 74 },
  { x: 2027, y: 82 },
];

// ── Year labels shown on X-axis ────────────────────────────────────────────
export const YEAR_LABELS = [2020, 2021, 2022, 2023, 2024, 2025, 2026, 2027];

// ── Animation frames ────────────────────────────────────────────────────────
export const TOTAL_FRAMES = 300;
export const FADE_IN_END = 30;
export const PULSE_START = 30;
export const REEMPH_START = 90;
export const REFRAME_TEXT_START = 150;
export const FADE_OUT_START = 270;
export const FADE_OUT_END = 300;
