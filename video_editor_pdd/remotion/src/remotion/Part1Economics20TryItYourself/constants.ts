// ── Colors ──────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const MAIN_TEXT_COLOR = "#E2E8F0";
export const INSTRUCTION_COLOR = "#94A3B8";
export const ACCENT_COLOR = "#4A90D9";
export const NOISE_COLOR = "#FFFFFF";

// ── Dimensions ──────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// ── Typography ──────────────────────────────────────────
export const MAIN_FONT_SIZE = 64;
export const INSTRUCTION_FONT_SIZE = 16;
export const INSTRUCTION_LINE_HEIGHT = 28;
export const MAIN_TEXT_ROTATION = -1.5; // degrees

// ── Positions ───────────────────────────────────────────
export const MAIN_TEXT_Y = 440;
export const INSTRUCTION_START_Y = 560;

// ── Opacity ─────────────────────────────────────────────
export const NOISE_OPACITY = 0.02;
export const UNDERLINE_OPACITY = 0.4;
export const INSTRUCTION_OPACITY = 0.6;
export const BOLD_INSTRUCTION_OPACITY = 0.8;

// ── Animation Timing (frames) ───────────────────────────
export const TOTAL_FRAMES = 240;
export const STROKE_WRITE_START = 0;
export const STROKE_WRITE_DURATION = 60;
export const UNDERLINE_START = 60;
export const UNDERLINE_DURATION = 30;
export const INSTRUCTION_LINE1_START = 90;
export const INSTRUCTION_LINE2_START = 110;
export const INSTRUCTION_LINE3_START = 130;
export const INSTRUCTION_FADE_DURATION = 20;

// ── Text Content ────────────────────────────────────────
export const MAIN_TEXT = "Try it yourself.";
export const INSTRUCTIONS = [
  "Give your favorite LLM a hard coding problem as code,",
  "then as natural language.",
  "The natural language version will win.",
] as const;
