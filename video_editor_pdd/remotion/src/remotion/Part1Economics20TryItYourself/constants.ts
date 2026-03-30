// constants.ts — Part1Economics20TryItYourself
// Colors, dimensions, and animation timing for the handwritten challenge card.

// ─── Canvas ───────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = "#0A0F1A";

// ─── Colors ───────────────────────────────────────────────────
export const CHALLENGE_TEXT_COLOR = "#E2E8F0";
export const INSTRUCTION_DIM_COLOR = "#94A3B8";
export const INSTRUCTION_BOLD_COLOR = "#E2E8F0";
export const UNDERLINE_COLOR = "#4A90D9";
export const NOISE_COLOR = "#FFFFFF";

// ─── Opacity ──────────────────────────────────────────────────
export const NOISE_OPACITY = 0.02;
export const UNDERLINE_OPACITY = 0.4;
export const INSTRUCTION_DIM_OPACITY = 0.6;
export const INSTRUCTION_BOLD_OPACITY = 0.8;

// ─── Typography ───────────────────────────────────────────────
export const CHALLENGE_FONT_SIZE = 64;
export const CHALLENGE_FONT_FAMILY =
  "'Caveat', 'Segoe Script', 'Comic Sans MS', cursive";
export const INSTRUCTION_FONT_SIZE = 16;
export const INSTRUCTION_FONT_FAMILY =
  "'Inter', -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif";
export const INSTRUCTION_LINE_HEIGHT = 28; // px between instruction lines

// ─── Positions ────────────────────────────────────────────────
export const CHALLENGE_Y = 440;
export const CHALLENGE_ROTATION_DEG = -1.5;
export const INSTRUCTION_START_Y = 560;

// ─── Animation Timing (frames @ 30fps) ───────────────────────
export const FPS = 30;
export const TOTAL_FRAMES = 240;

// Stroke-reveal for "Try it yourself."
export const STROKE_START = 0;
export const STROKE_DURATION = 60;

// Wavy underline draw
export const UNDERLINE_START = 60;
export const UNDERLINE_DURATION = 30;

// Instruction lines fade-in
export const LINE1_START = 90;
export const LINE2_START = 110;
export const LINE3_START = 130;
export const LINE_FADE_DURATION = 20;

// ─── Instruction text content ─────────────────────────────────
export const INSTRUCTIONS: readonly { text: string; bold: boolean }[] = [
  {
    text: "Give your favorite LLM a hard coding problem as code,",
    bold: false,
  },
  { text: "then as natural language.", bold: false },
  { text: "The natural language version will win.", bold: true },
] as const;
