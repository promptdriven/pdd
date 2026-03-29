// constants.ts — colors, dimensions, module data for Context Compression animation

// ── Colors ──────────────────────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const WINDOW_BORDER_COLOR = "#4A90D9";
export const WINDOW_GLOW_COLOR = "rgba(74, 144, 217, 0.1)";

export const CODE_BLOCK_FILL = "#1E293B";
export const CODE_BLOCK_BORDER = "#334155";
export const CODE_LABEL_COLOR = "#64748B";

export const PROMPT_BLOCK_FILL = "rgba(74, 144, 217, 0.15)";
export const PROMPT_BLOCK_BORDER = "#4A90D9";

export const OVERFLOW_RED = "#EF4444";
export const OVERFLOW_GLOW = "rgba(239, 68, 68, 0.1)";

export const REMAINING_GREEN = "#5AAA6E";
export const REMAINING_GREEN_FILL = "rgba(90, 170, 110, 0.05)";

export const PHASE_LABEL_COLOR = "#E2E8F0";

// ── Canvas ──────────────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 1380;
export const FPS = 30;

// ── Context Window ──────────────────────────────────────────────────────────
export const WINDOW_WIDTH = 500;
export const WINDOW_HEIGHT = 700;
export const WINDOW_CENTER_X = 960;
export const WINDOW_CENTER_Y = 480;
export const WINDOW_LEFT = WINDOW_CENTER_X - WINDOW_WIDTH / 2; // 710
export const WINDOW_TOP = WINDOW_CENTER_Y - WINDOW_HEIGHT / 2; // 130
export const WINDOW_BORDER_RADIUS = 8;
export const WINDOW_BORDER_WIDTH = 2;

// ── Module Data ─────────────────────────────────────────────────────────────
export const MODULE_NAMES = [
  "auth",
  "parser",
  "router",
  "validator",
  "logger",
  "cache",
  "queue",
  "mailer",
  "search",
  "analytics",
  "billing",
  "permissions",
  "notifications",
  "export",
  "import",
  "scheduler",
  "webhook",
  "api_client",
  "transformer",
  "serializer",
];

// Heights for code blocks (varying, 180-350px) — total ~5000px
export const CODE_BLOCK_HEIGHTS = [
  280, 320, 240, 350, 200, 310, 180, 290, 260, 330, 220, 300, 270, 190, 340,
  250, 210, 285, 230, 295,
];

export const PROMPT_BLOCK_HEIGHT = 30;
export const PROMPT_BLOCK_GAP = 3;
export const CODE_BLOCK_GAP = 4;

// Number of code blocks that fit in window
export const BLOCKS_THAT_FIT = 3;
export const OVERFLOW_COUNT = 17;

// ── Animation Timing (frames) ───────────────────────────────────────────────
export const PHASE_WINDOW_DRAW_START = 0;
export const PHASE_WINDOW_DRAW_END = 60;

export const PHASE_CODE_SLIDE_START = 60;
export const PHASE_CODE_SLIDE_END = 300;
export const CODE_SLIDE_STAGGER = 15; // frames between each block

export const PHASE_OVERFLOW_HOLD_START = 300;
export const PHASE_OVERFLOW_HOLD_END = 420;

export const PHASE_COMPRESS_START = 420;
export const PHASE_COMPRESS_END = 600;

export const PHASE_RESULT_START = 600;
export const PHASE_RESULT_END = 780;

export const PHASE_FINAL_HOLD_START = 780;
export const PHASE_FINAL_HOLD_END = 1380;
