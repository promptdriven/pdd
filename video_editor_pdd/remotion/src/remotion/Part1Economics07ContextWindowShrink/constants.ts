// ── Colors ──────────────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const BLOCK_FILL = "#1E293B";
export const BLOCK_BORDER = "#334155";
export const CONTEXT_BORDER_COLOR = "#4A90D9";
export const LABEL_COLOR = "#94A3B8";

export const COVERAGE_GREEN = "#5AAA6E";
export const COVERAGE_AMBER = "#F59E0B";
export const COVERAGE_RED = "#EF4444";
export const COVERAGE_DARK_RED = "#DC2626";

export const HIGHLIGHT_RED = "#EF4444";
export const HIGHLIGHT_GREEN = "#5AAA6E";

// ── Dimensions ──────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

export const CONTEXT_WINDOW_WIDTH = 280;
export const CONTEXT_WINDOW_HEIGHT = 240;

export const BLOCK_GAP = 4;

// ── Grid Area (centered region where grids are drawn) ───────────────
export const GRID_CENTER_X = CANVAS_WIDTH / 2;
export const GRID_CENTER_Y = CANVAS_HEIGHT / 2 + 20; // slightly below center

// ── Growth stages ───────────────────────────────────────────────────
export interface GrowthStage {
  gridSize: number;
  coverage: number;
  coverageColor: string;
  startFrame: number;
  transitionFrames: number;
}

export const GROWTH_STAGES: GrowthStage[] = [
  { gridSize: 4,  coverage: 80, coverageColor: COVERAGE_GREEN,    startFrame: 0,   transitionFrames: 60 },
  { gridSize: 8,  coverage: 40, coverageColor: COVERAGE_AMBER,    startFrame: 180, transitionFrames: 60 },
  { gridSize: 16, coverage: 10, coverageColor: COVERAGE_RED,      startFrame: 300, transitionFrames: 60 },
  { gridSize: 32, coverage: 2,  coverageColor: COVERAGE_DARK_RED, startFrame: 420, transitionFrames: 60 },
];

// ── Frame milestones ────────────────────────────────────────────────
export const TOTAL_FRAMES = 1560;
export const MISMATCH_START_FRAME = 720;
export const MISMATCH_FADE_FRAMES = 20;

// ── Mismatch block indices (within the 32×32 grid) ─────────────────
// Red blocks: inside context window but irrelevant
export const RED_BLOCK_INDICES = [3, 7, 11, 14];
// Green blocks: outside context window but needed
export const GREEN_BLOCK_INDICES = [45, 128, 312, 567, 890, 1002];

// ── Coverage counter position ───────────────────────────────────────
export const COUNTER_X = 1600;
export const COUNTER_Y = 100;
