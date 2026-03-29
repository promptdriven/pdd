// === Colors ===
export const BG_COLOR = '#0A0F1A';
export const PANEL_BG = '#0F172A';

// Left panel (Agentic Patching)
export const LEFT_HEADER_COLOR = '#94A3B8';
export const LEFT_BORDER_COLOR = '#64748B';
export const BLOCK_RED = '#EF4444';
export const BLOCK_GREEN_RELEVANT = '#5AAA6E';
export const BLOCK_GRAY = '#334155';

// Right panel (PDD Regeneration)
export const RIGHT_HEADER_COLOR = '#4A90D9';
export const RIGHT_BORDER_COLOR = '#4A90D9';
export const PROMPT_BLUE = '#4A90D9';
export const TEST_AMBER = '#D9944A';
export const GROUNDING_GREEN = '#5AAA6E';

// Labels
export const LABEL_RED = '#EF4444';
export const LABEL_GREEN = '#5AAA6E';
export const ROOM_TO_THINK_COLOR = '#64748B';

// === Layout ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

export const PANEL_WIDTH = 860;
export const PANEL_HEIGHT = 600;

export const LEFT_PANEL_X = 60;
export const LEFT_PANEL_Y = 200;

export const RIGHT_PANEL_X = 1000;
export const RIGHT_PANEL_Y = 200;

// === Token block grid (left panel) ===
export const TOKEN_ROWS = 15;
export const TOKEN_COLS = 20;
export const TOKEN_BLOCK_GAP = 4;

// === Right panel blocks ===
export const PROMPT_HEIGHT = 60;
export const TEST_HEIGHT = 100;
export const GROUNDING_HEIGHT = 40;
export const BLOCK_PADDING = 16;

// === Animation timing (frames) ===
export const PANEL_DRAW_START = 0;
export const PANEL_DRAW_END = 60;
export const LEFT_FILL_START = 60;
export const LEFT_FILL_END = 210;
export const RIGHT_SLIDE_START = 210;
export const RIGHT_PROMPT_START = 210;
export const RIGHT_TEST_START = 250;
export const RIGHT_GROUNDING_START = 290;
export const ROOM_LABEL_START = 330;
export const COMPARISON_LABEL_START = 360;
export const TOTAL_FRAMES = 810;

// === Distribution ===
export const DISTRIBUTION = {
  irrelevant: 0.80,
  relevant: 0.05,
  neutral: 0.15,
} as const;
