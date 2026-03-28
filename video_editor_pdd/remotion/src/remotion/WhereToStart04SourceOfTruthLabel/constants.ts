// ── Canvas ──
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = "#0A0F1A";
export const TOTAL_FRAMES = 150;
export const FPS = 30;

// ── Colors ──
export const GREEN_ACCENT = "#5AAA6E";
export const TEXT_LIGHT = "#E2E8F0";
export const TEXT_MUTED = "#94A3B8";
export const TEXT_DIM = "#64748B";
export const TERMINAL_BG = "#0D1117";

// ── Prompt File ──
export const PROMPT_FILE_X = 750;
export const PROMPT_FILE_Y = 350;
export const PROMPT_FILE_WIDTH = 400;
export const PROMPT_FILE_HEIGHT = 250;
export const PROMPT_FILE_BORDER = 2.5;
export const PROMPT_FILE_RADIUS = 6;
export const PROMPT_GLOW_BLUR = 20;
export const PROMPT_GLOW_OPACITY = 0.12;
export const PROMPT_FILE_NAME = "auth_handler.prompt.md";

// ── Gray Code File ──
export const GRAY_FILE_X = 200;
export const GRAY_FILE_Y = 400;
export const GRAY_FILE_WIDTH = 200;
export const GRAY_FILE_HEIGHT = 150;
export const GRAY_FILE_OPACITY_START = 0.1;
export const GRAY_FILE_OPACITY_END = 0.04;
export const GRAY_FILE_NAME = "auth_handler.py";

// ── Terminal ──
export const TERMINAL_X = 750;
export const TERMINAL_Y = 650;
export const TERMINAL_WIDTH = 500;
export const TERMINAL_HEIGHT = 80;
export const TERMINAL_RADIUS = 4;

// ── Badge ──
export const BADGE_X = 950;
export const BADGE_Y = 260;
export const BADGE_TEXT = "SOURCE OF TRUTH";
export const BADGE_BG_OPACITY = 0.15;
export const BADGE_BORDER_WIDTH = 1.5;
export const BADGE_RADIUS = 20;
export const BADGE_LETTER_SPACING = 2;

// ── Animation Frames ──
export const TERMINAL_FADE_START = 0;
export const TERMINAL_FADE_DURATION = 15;

export const CMD_GENERATE_START = 15;
export const CMD_GENERATE_TEXT = "pdd generate auth_handler.py";
export const CHARS_PER_FRAME = 1 / 3; // 3 frames per character

export const SHIMMER_START = 45;
export const SHIMMER_DURATION = 15;

export const CMD_TEST_START = 60;
export const CMD_TEST_TEXT = "pdd test";

export const CHECKMARK_START = 75;
export const CHECKMARK_DURATION = 15;
export const CHECKMARK_TEXT = "✓ All tests pass";

export const BADGE_START = 90;
export const BADGE_DURATION = 20;

export const RECEDE_START = 120;
export const RECEDE_DURATION = 30;

// ── Markdown Lines (faux content for prompt file) ──
export const MARKDOWN_LINES = [
  "# Auth Handler",
  "",
  "## Purpose",
  "Handle user authentication via",
  "JWT tokens with refresh flow.",
  "",
  "## Constraints",
  "- Session timeout: 30min",
  "- Rate limit: 100 req/min",
  "- Must validate CORS origin",
];
