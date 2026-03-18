// === Colors ===
export const BG_COLOR = '#0A0F1A';
export const BLUE = '#4A90D9';
export const GRAY = '#94A3B8';
export const BLUE_GRAY = '#6B8AB5';
export const MID_GRAY = '#8094A8';
export const TEXT_PRIMARY = '#E2E8F0';
export const BORDER_COLOR = '#334155';
export const GREEN = '#5AAA6E';
export const STRIKE_COLOR = '#64748B';

// === Canvas ===
export const WIDTH = 1920;
export const HEIGHT = 1080;

// === Spectrum Bar ===
export const BAR_X = 360;
export const BAR_Y = 500;
export const BAR_WIDTH = 1200;
export const BAR_HEIGHT = 60;
export const BAR_RADIUS = 8;

// === Slider ===
export const SLIDER_X = 660; // ~25% from left edge
export const SLIDER_WIDTH = 4;
export const SLIDER_HEIGHT = 80;
export const SLIDER_Y = BAR_Y - 10; // extends 10px above bar

// === Notch positions (x coordinates) ===
export const NOTCH_POSITIONS = [1200, 1350, 1500];
export const NOTCH_SIZE = 6;

// === Region Labels ===
export const REGIONS = [
  { label: 'Architecture, intent, constraints', x: 500, y: 400, color: BLUE },
  { label: 'Edge cases, error handling', x: 780, y: 420, color: BLUE_GRAY },
  { label: 'Algorithm choice, tuning', x: 1150, y: 400, color: MID_GRAY },
  { label: 'Bit-level ops, inner loops', x: 1450, y: 420, color: GRAY },
] as const;

// === Animation Timing (frames) ===
export const TIMING = {
  // Phase 1: Spectrum bar draws (0-30)
  barDrawStart: 0,
  barDrawDuration: 30,

  // Phase 2: Region labels (30-60)
  regionStart: 30,
  regionStagger: 10,
  regionFadeDuration: 15,

  // Phase 3: Slider appears (60-120)
  sliderStart: 60,

  // Phase 4: Notches (120-150)
  notchStart: 120,
  notchStagger: 8,
  notchFadeDuration: 8,

  // Phase 5: Line 1 (150-200)
  line1Start: 150,
  textFadeDuration: 20,
  strikethroughDelay: 10,
  strikethroughDuration: 15,

  // Phase 6: Line 2 (200-260)
  line2Start: 200,

  // Phase 7: Line 3 (260-320)
  line3Start: 260,

  // Phase 8: Hold (320-360)
  totalFrames: 360,

  // Slider pulse cycle
  sliderPulseCycle: 40,
} as const;
