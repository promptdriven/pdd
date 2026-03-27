// ── Colors ──────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";

export const BLOCK_FILL = "#1E293B";
export const BLOCK_BORDER = "#334155";

export const WINDOW_BORDER_COLOR = "#4A90D9";
export const WINDOW_GLOW_OPACITY = 0.2;
export const WINDOW_GLOW_BLUR = 12;
export const WINDOW_TINT_OPACITY = 0.05;

export const LABEL_COLOR = "#94A3B8";

export const RED_HIGHLIGHT = "#EF4444";
export const GREEN_HIGHLIGHT = "#5AAA6E";

// ── Dimensions ──────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

export const CONTEXT_WINDOW_WIDTH = 280;
export const CONTEXT_WINDOW_HEIGHT = 240;

// Per-stage grid pixel dimensions (total grid extent including gaps)
// Designed so the context window (280×240) covers decreasing fractions.
export const GRID_STAGE_SIZES: Record<number, { blockPx: number; gapPx: number }> = {
  4: { blockPx: 60, gapPx: 4 },   // total: 4*60 + 3*4 = 252px  → window covers ~80%
  8: { blockPx: 50, gapPx: 3 },   // total: 8*50 + 7*3 = 421px  → window covers ~40%
  16: { blockPx: 38, gapPx: 2 },  // total: 16*38 + 15*2 = 638px → window covers ~10%
  32: { blockPx: 28, gapPx: 1 },  // total: 32*28 + 31*1 = 927px → window covers ~2%
};

// ── Growth Stages ───────────────────────────────────────
export interface GrowthStage {
  gridSize: number;
  startFrame: number;
  coveragePercent: number;
  coverageColor: string;
}

export const GROWTH_STAGES: GrowthStage[] = [
  { gridSize: 4, startFrame: 0, coveragePercent: 80, coverageColor: "#5AAA6E" },
  { gridSize: 8, startFrame: 180, coveragePercent: 40, coverageColor: "#F59E0B" },
  { gridSize: 16, startFrame: 300, coveragePercent: 10, coverageColor: "#EF4444" },
  { gridSize: 32, startFrame: 420, coveragePercent: 2, coverageColor: "#DC2626" },
];

// ── Timing ──────────────────────────────────────────────
export const TOTAL_FRAMES = 1560;
export const TRANSITION_FRAMES = 60;
export const MISMATCH_START_FRAME = 720;
export const HIGHLIGHT_FADE_FRAMES = 20;

// ── Mismatch Blocks ─────────────────────────────────────
// Indices within the 32×32 grid (0-indexed, row-major)
// Context window covers roughly rows 12-20, cols 11-20 in the 32×32 grid.
// Red blocks: inside the context window but irrelevant
export const RED_BLOCK_INDICES = [430, 492, 562, 623]; // (13,14) (15,12) (17,18) (19,15)
// Green blocks: outside the context window but needed
export const GREEN_BLOCK_INDICES = [69, 156, 259, 775, 921, 970]; // scattered outside

export const HIGHLIGHT_OVERLAY_OPACITY = 0.3;

// ── Counter Position ────────────────────────────────────
export const COUNTER_X = 1600;
export const COUNTER_Y = 100;
