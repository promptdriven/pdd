// Component-level constants for AnimationSection04SquareSlideRight

export const CANVAS = {
  width: 1280,
  height: 720,
} as const;

export const COLORS = {
  background: '#141921',
  square: '#22C55E',
  glow: 'rgba(34, 197, 94, 0.2)',
} as const;

export const SQUARE = {
  size: 160,
  borderRadius: 8,
} as const;

export const MOTION = {
  startX: 640,
  targetX: 920,
  overshootX: 935,
  centerY: 360,
} as const;

export const TRAILS = [
  { offset: 40, delay: 3, opacity: 0.15 },
  { offset: 80, delay: 6, opacity: 0.10 },
  { offset: 120, delay: 9, opacity: 0.06 },
  { offset: 160, delay: 12, opacity: 0.03 },
] as const;

export const TIMING = {
  // Phase 1: Hold at center, guide line fades in (frames 0-3)
  holdEnd: 3,

  // Phase 2: Slide from center to overshoot (frames 3-22)
  slideStart: 3,
  slideEnd: 22,

  // Phase 3: Overshoot settle back to target (frames 22-27)
  settleStart: 22,
  settleEnd: 27,

  // Phase 4: Guide line fades out, glow appears (frames 27-33)
  fadeStart: 27,
  fadeEnd: 33,

  totalDuration: 33,
} as const;

export const GLOW = {
  blur: 30,
} as const;

export const FPS = 30;
