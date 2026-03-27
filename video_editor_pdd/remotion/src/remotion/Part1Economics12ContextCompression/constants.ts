// constants.ts — colors, dimensions, module data for Context Compression animation

// ── Canvas ──
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BG_COLOR = "#0A0F1A";

// ── Context Window Frame ──
export const WINDOW_WIDTH = 500;
export const WINDOW_HEIGHT = 700;
export const WINDOW_CENTER_X = 960;
export const WINDOW_CENTER_Y = 480;
export const WINDOW_LEFT = WINDOW_CENTER_X - WINDOW_WIDTH / 2; // 710
export const WINDOW_TOP = WINDOW_CENTER_Y - WINDOW_HEIGHT / 2; // 130
export const WINDOW_BORDER_COLOR = "#4A90D9";
export const WINDOW_BORDER_WIDTH = 2;
export const WINDOW_BORDER_RADIUS = 8;
export const WINDOW_GLOW_COLOR = "rgba(74,144,217,0.1)";
export const WINDOW_GLOW_BLUR = 8;

// ── Module list ──
export const MODULES = [
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
] as const;

export const MODULE_COUNT = MODULES.length; // 20

// ── Code block heights (Phase 1) — varying between 180–350px ──
// Deterministic pseudo-random heights for 20 modules
export const CODE_BLOCK_HEIGHTS = [
  240, 310, 200, 280, 190, 340, 220, 260, 300, 180,
  350, 230, 270, 320, 210, 290, 250, 330, 195, 285,
];

// ── Code Blocks (Phase 1) ──
export const CODE_BLOCK_FILL = "#1E293B";
export const CODE_BLOCK_BORDER = "#334155";
export const CODE_BLOCK_LABEL_COLOR = "#64748B";
export const CODE_BLOCK_GAP = 4; // gap between stacked blocks

// ── Prompt Blocks (Phase 2) ──
export const PROMPT_BLOCK_HEIGHT = 30;
export const PROMPT_BLOCK_FILL = "rgba(74,144,217,0.15)";
export const PROMPT_BLOCK_BORDER = "#4A90D9";
export const PROMPT_BLOCK_GAP = 3;

// Total stacked heights
export const TOTAL_CODE_HEIGHT =
  CODE_BLOCK_HEIGHTS.reduce((a, b) => a + b, 0) +
  (MODULE_COUNT - 1) * CODE_BLOCK_GAP; // ~5276px
export const TOTAL_PROMPT_HEIGHT =
  MODULE_COUNT * PROMPT_BLOCK_HEIGHT +
  (MODULE_COUNT - 1) * PROMPT_BLOCK_GAP; // 657px

// ── Overflow ──
export const OVERFLOW_COLOR = "#EF4444";
export const OVERFLOW_COUNT = 17;

// ── Remaining Space ──
export const REMAINING_SPACE_COLOR = "#5AAA6E";

// ── Typography colors ──
export const LABEL_COLOR = "#E2E8F0";
export const RATIO_COLOR = "#5AAA6E";

// ── Frame Timing ──
export const TOTAL_FRAMES = 1380;
export const FPS = 30;

// Phase boundaries
export const FRAME_WINDOW_DRAW_START = 0;
export const FRAME_WINDOW_DRAW_END = 60;

export const FRAME_CODE_SLIDE_START = 60;
export const FRAME_CODE_SLIDE_END = 300;

export const FRAME_OVERFLOW_APPEAR = 300;
export const FRAME_OVERFLOW_HOLD_END = 420;

export const FRAME_COMPRESS_START = 420;
export const FRAME_COMPRESS_END = 600;

export const FRAME_RESULT_APPEAR = 600;
export const FRAME_RESULT_HOLD_START = 780;

// Visible modules that fit in the window in code form
export const VISIBLE_CODE_MODULES = 3; // first 3 fit, rest overflow
