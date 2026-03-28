// Closing06TheBeat – constants
// A deliberate pause / "the beat" between final narration and closing title card

// === Canvas ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 60;

// === Background Colors ===
export const BG_DEEP_NAVY = '#0A0F1A';
export const BG_TRUE_BLACK = '#000000';

// === Horizontal Rule ===
export const RULE_COLOR = '#334155';
export const RULE_MAX_OPACITY = 0.15;
export const RULE_WIDTH = 200;
export const RULE_HEIGHT = 1;
export const RULE_CENTER_X = CANVAS_WIDTH / 2;
export const RULE_CENTER_Y = CANVAS_HEIGHT / 2;

// === Animation Timing (frames) ===
export const HOLD_END = 15;          // Frames 0-15: quiet hold
export const RULE_FADE_IN_START = 15; // Frame 15: rule begins fading in
export const RULE_FADE_IN_DURATION = 15; // 15 frames to fade in (frames 15-30)
export const BG_DARKEN_START = 30;   // Frame 30: background starts darkening
export const BG_DARKEN_DURATION = 30; // 30 frames to reach true black (frames 30-60)
export const RULE_FADE_OUT_START = 45; // Frame 45: rule begins fading out
export const RULE_FADE_OUT_DURATION = 15; // 15 frames to fade out (frames 45-60)
