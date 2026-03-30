// constants.ts — Colors, dimensions, and module data for context compression animation

// ─── Canvas ────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = "#0A0F1A";

// ─── Duration ──────────────────────────────────────────────────────
export const TOTAL_FRAMES = 1380;
export const FPS = 30;

// ─── Context Window Frame ──────────────────────────────────────────
export const WINDOW_WIDTH = 500;
export const WINDOW_HEIGHT = 700;
export const WINDOW_CENTER_X = 960;
export const WINDOW_CENTER_Y = 480;
export const WINDOW_LEFT = WINDOW_CENTER_X - WINDOW_WIDTH / 2;
export const WINDOW_TOP = WINDOW_CENTER_Y - WINDOW_HEIGHT / 2;
export const WINDOW_BORDER_COLOR = "#4A90D9";
export const WINDOW_BORDER_WIDTH = 2;
export const WINDOW_BORDER_RADIUS = 8;
export const WINDOW_GLOW_OPACITY = 0.1;
export const WINDOW_GLOW_BLUR = 8;

// ─── Modules ───────────────────────────────────────────────────────
export const MODULE_NAMES = [
  "auth", "parser", "router", "validator", "logger",
  "cache", "queue", "mailer", "search", "analytics",
  "billing", "permissions", "notifications", "export",
  "import", "scheduler", "webhook", "api_client",
  "transformer", "serializer",
] as const;

export const MODULE_COUNT = MODULE_NAMES.length;
export const OVERFLOW_COUNT = 17;
export const MODULES_THAT_FIT = MODULE_COUNT - OVERFLOW_COUNT; // 3

// ─── Code Block Dimensions ─────────────────────────────────────────
export const CODE_BLOCK_FILL = "#1E293B";
export const CODE_BLOCK_BORDER = "#334155";
export const CODE_BLOCK_BORDER_WIDTH = 1;
export const CODE_BLOCK_GAP = 4;

// Deterministic heights for the 20 code blocks (180–350px range)
export const CODE_BLOCK_HEIGHTS = [
  280, 220, 310, 250, 195,
  340, 230, 265, 300, 185,
  320, 275, 245, 350, 210,
  290, 260, 335, 200, 305,
];

// ─── Prompt Block Dimensions ───────────────────────────────────────
export const PROMPT_BLOCK_HEIGHT = 30;
export const PROMPT_BLOCK_GAP = 3;
export const PROMPT_BLOCK_FILL_COLOR = "#4A90D9";
export const PROMPT_BLOCK_FILL_OPACITY = 0.15;
export const PROMPT_BLOCK_BORDER_COLOR = "#4A90D9";

// ─── Overflow Indicator ────────────────────────────────────────────
export const OVERFLOW_COLOR = "#EF4444";
export const OVERFLOW_DASH = "6 4";
export const OVERFLOW_LINE_WIDTH = 1.5;

// ─── Remaining Space Indicator ─────────────────────────────────────
export const REMAINING_SPACE_COLOR = "#5AAA6E";

// ─── Typography ────────────────────────────────────────────────────
export const FONT_FAMILY = "Inter, sans-serif";
export const MODULE_LABEL_SIZE = 11;
export const MODULE_LABEL_COLOR = "#64748B";
export const OVERFLOW_LABEL_SIZE = 14;
export const PHASE_LABEL_SIZE = 18;
export const PHASE_LABEL_COLOR = "#E2E8F0";
export const RATIO_LABEL_SIZE = 20;

// ─── Animation Timing (frame numbers) ─────────────────────────────
export const PHASE_WINDOW_DRAW_START = 0;
export const PHASE_WINDOW_DRAW_END = 60;
export const PHASE_CODE_SLIDE_START = 60;
export const PHASE_CODE_SLIDE_END = 300;
export const PHASE_OVERFLOW_HOLD_START = 300;
export const PHASE_OVERFLOW_HOLD_END = 420;
export const PHASE_COMPRESS_START = 420;
export const PHASE_COMPRESS_END = 600;
export const PHASE_RESULT_START = 600;
export const PHASE_RESULT_END = 780;
export const PHASE_FINAL_HOLD_START = 780;
export const PHASE_FINAL_HOLD_END = 1380;

// Stagger for code block entrance
export const CODE_SLIDE_STAGGER = 15;
export const CODE_SLIDE_DURATION_PER_BLOCK = 30;
