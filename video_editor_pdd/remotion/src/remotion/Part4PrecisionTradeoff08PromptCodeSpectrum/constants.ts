// ─── Colors ───
export const BG_COLOR = '#0A0F1A';
export const BLUE = '#4A90D9';
export const GRAY = '#94A3B8';
export const BLUE_GRAY = '#6B8AB5';
export const MID_GRAY = '#8094A8';
export const TEXT_PRIMARY = '#E2E8F0';
export const TEXT_DIM = '#64748B';
export const BORDER_COLOR = '#334155';
export const GREEN = '#5AAA6E';
export const SLIDER_GLOW_COLOR = '#4A90D9';

// ─── Canvas ───
export const WIDTH = 1920;
export const HEIGHT = 1080;

// ─── Spectrum Bar ───
export const BAR_X = 360;
export const BAR_Y = 500;
export const BAR_WIDTH = 1200;
export const BAR_HEIGHT = 60;
export const BAR_RADIUS = 8;

// ─── Slider ───
export const SLIDER_X = 660; // ~25% from left edge
export const SLIDER_HEIGHT = 80;
export const SLIDER_WIDTH = 4;

// ─── Region labels ───
export const REGIONS = [
  { label: 'Architecture, intent, constraints', color: BLUE, x: 500, y: 400 },
  { label: 'Edge cases, error handling', color: BLUE_GRAY, x: 780, y: 420 },
  { label: 'Algorithm choice, tuning', color: MID_GRAY, x: 1150, y: 400 },
  { label: 'Bit-level ops, inner loops', color: GRAY, x: 1450, y: 420 },
] as const;

// ─── Code-dip notches ───
export const NOTCH_POSITIONS = [1200, 1350, 1500] as const;
export const NOTCH_SIZE = 6;

// ─── Animation Timing (frames) ───
export const ANIM = {
  // Phase 1: Spectrum bar draws from center
  barDrawStart: 0,
  barDrawDuration: 30,

  // Phase 2: Region labels fade in
  regionStart: 30,
  regionStagger: 10,
  regionFadeDuration: 15,

  // Phase 3: Slider appears
  sliderStart: 60,

  // Phase 4: Notches appear
  notchStart: 120,
  notchStagger: 8,
  notchFadeDuration: 8,

  // Phase 5: Key question line 1
  line1Start: 150,
  line1FadeDuration: 20,
  strikethroughDelay: 10,
  strikethroughDuration: 15,

  // Phase 6: Key question line 2
  line2Start: 200,
  line2FadeDuration: 20,

  // Phase 7: Answer line 3
  line3Start: 260,
  line3FadeDuration: 20,

  // Total duration
  total: 360,
} as const;
