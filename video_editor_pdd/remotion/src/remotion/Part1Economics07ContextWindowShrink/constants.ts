// constants.ts — Part1Economics07ContextWindowShrink
// All colors, dimensions, and animation timing for the context window shrink visualization.

// ─── Canvas ──────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = '#0A0F1A';

// ─── Duration ────────────────────────────────────────────────────────
export const TOTAL_FRAMES = 1560;
export const FPS = 30;

// ─── Code Grid ───────────────────────────────────────────────────────
export const BLOCK_FILL = '#1E293B';
export const BLOCK_BORDER = '#334155';
export const BLOCK_GAP = 4;
export const INITIAL_BLOCK_SIZE = 60; // px per block at 4×4

// Grid center — slight left of center to leave room for counter
export const GRID_CENTER_X = 880;
export const GRID_CENTER_Y = 540;

// ─── Growth Stages ───────────────────────────────────────────────────
export interface GrowthStage {
  gridSize: number;
  startFrame: number;
  coveragePercent: number;
  coverageColor: string;
}

export const GROWTH_STAGES: GrowthStage[] = [
  { gridSize: 4, startFrame: 0, coveragePercent: 80, coverageColor: '#5AAA6E' },
  { gridSize: 8, startFrame: 180, coveragePercent: 40, coverageColor: '#F59E0B' },
  { gridSize: 16, startFrame: 300, coveragePercent: 10, coverageColor: '#EF4444' },
  { gridSize: 32, startFrame: 420, coveragePercent: 2, coverageColor: '#DC2626' },
];

export const TRANSITION_DURATION = 60; // frames per grid transition

// ─── Context Window ──────────────────────────────────────────────────
export const CTX_WINDOW_WIDTH = 280;
export const CTX_WINDOW_HEIGHT = 240;
export const CTX_BORDER_COLOR = '#4A90D9';
export const CTX_BORDER_WIDTH = 2;
export const CTX_GLOW_OPACITY = 0.2;
export const CTX_GLOW_BLUR = 12;
export const CTX_FILL_OPACITY = 0.05;

// ─── Coverage Counter ────────────────────────────────────────────────
export const COUNTER_X = 1600;
export const COUNTER_Y = 100;
export const COUNTER_LABEL_COLOR = '#94A3B8';
export const COUNTER_LABEL_SIZE = 14;
export const COUNTER_VALUE_SIZE = 36;

// ─── Mismatch Highlights ────────────────────────────────────────────
export const MISMATCH_START_FRAME = 720;
export const HIGHLIGHT_FADE_DURATION = 20;
export const RED_HIGHLIGHT_COLOR = '#EF4444';
export const GREEN_HIGHLIGHT_COLOR = '#5AAA6E';
export const HIGHLIGHT_OVERLAY_OPACITY = 0.3;

// Red blocks: flat indices inside the context window (at 32×32)
export const RED_BLOCK_INDICES = [3, 7, 11, 14];

// Green blocks: flat indices outside the context window (at 32×32)
export const GREEN_BLOCK_INDICES = [45, 128, 312, 567, 890, 1002];

// ─── Tooltip Labels ─────────────────────────────────────────────────
export const TOOLTIP_FONT_SIZE = 11;
export const RED_TOOLTIP_LABEL = 'Irrelevant';
export const GREEN_TOOLTIP_LABEL = 'Needed';
