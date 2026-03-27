// Part1Economics10ForkCodebaseSize — constants & data

// ── Canvas ──────────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 1380;

// ── Background ──────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";

// ── Chart layout (matches spec 03 style) ────────────────
export const CHART_LEFT = 180;
export const CHART_RIGHT = 1780;
export const CHART_TOP = 140;
export const CHART_BOTTOM = 900;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// ── Axis ranges ─────────────────────────────────────────
export const X_MIN = 2014;
export const X_MAX = 2026;
export const Y_MIN = 0;
export const Y_MAX = 0.6; // developer-hours scale (relative)

// ── Colors ──────────────────────────────────────────────
export const AXIS_COLOR = "#475569";
export const AXIS_LABEL_COLOR = "#94A3B8";
export const GRID_COLOR = "#1E293B";

export const GENERATE_LINE_COLOR = "#3B82F6"; // blue — generate line
export const PATCH_LINE_COLOR = "#F59E0B";    // amber — original patch line (pre-fork)

export const SMALL_CODEBASE_COLOR = "#5AAA6E";
export const LARGE_CODEBASE_COLOR = "#EF4444";

export const ARROW_COLOR = "#F59E0B";
export const CONTEXT_LABEL_COLOR = "#94A3B8";

// ── Line widths ─────────────────────────────────────────
export const MAIN_LINE_WIDTH = 3;
export const ARROW_LINE_WIDTH = 2;

// ── Typography ──────────────────────────────────────────
export const FONT_FAMILY = "Inter, system-ui, -apple-system, sans-serif";

// ── Pre-fork patch line (amber, from ~2014 to 2020) ─────
export const PATCH_LINE_DATA = [
  { x: 2014, y: 0.55 },
  { x: 2016, y: 0.52 },
  { x: 2018, y: 0.50 },
  { x: 2020, y: 0.48 },
];

// ── Generate cost line (blue, from 2014 to 2026) ────────
export const GENERATE_LINE_DATA = [
  { x: 2014, y: 0.10 },
  { x: 2016, y: 0.08 },
  { x: 2018, y: 0.06 },
  { x: 2020, y: 0.04 },
  { x: 2022, y: 0.03 },
  { x: 2024, y: 0.02 },
  { x: 2026, y: 0.015 },
];

// ── Fork data ───────────────────────────────────────────
export const FORK_POINT = { x: 2020, y: 0.48 };

export const SMALL_CODEBASE_DATA = [
  { x: 2020, y: 0.48 },
  { x: 2022, y: 0.30 },
  { x: 2024, y: 0.18 },
  { x: 2026, y: 0.10 },
];

export const LARGE_CODEBASE_DATA = [
  { x: 2020, y: 0.48 },
  { x: 2022, y: 0.47 },
  { x: 2024, y: 0.46 },
  { x: 2026, y: 0.45 },
];

// ── Debt-shaded area (between generate & patch/large) ───
// Fill area between generate and patch/large codebase line

// ── Y-axis tick marks ───────────────────────────────────
export const Y_TICKS = [0, 0.1, 0.2, 0.3, 0.4, 0.5, 0.6];
export const X_TICKS = [2014, 2016, 2018, 2020, 2022, 2024, 2026];

// ── Animation timing (frames) ───────────────────────────
export const PHASE_CHART_IN_START = 0;
export const PHASE_CHART_IN_END = 90;

export const PHASE_FORK_START = 90;
export const PHASE_FORK_END = 210;
export const FORK_DURATION = 120; // frames for the fork to diverge

export const PHASE_CONTEXT_LABEL_START = 180;

export const PHASE_DIVERGE_START = 210;
export const PHASE_DIVERGE_END = 420;

export const PHASE_METR_ANNOTATION_START = 420;
export const PHASE_PERCEPTION_ANNOTATION_START = 540;

export const PHASE_ARROW_START = 900;
export const PHASE_ARROW_END = 990;
export const ARROW_DRAW_DURATION = 90;

export const PHASE_ARROW_LABEL_START = 960;

export const FADE_DURATION = 20;
