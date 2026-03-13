// Component-level constants for AnimationSection03CircleToSquareMorph

export const CANVAS = {
  width: 1280,
  height: 720,
} as const;

export const COLORS = {
  background: '#141921',
  circleBlue: '#3B82F6',
  squareGreen: '#22C55E',
  blueShadow: 'rgba(59, 130, 246, 0.3)',
  greenShadow: 'rgba(34, 197, 94, 0.3)',
} as const;

export const DIMENSIONS = {
  circleSize: 180,
  squareSize: 160,
  circleBorderRadius: 90, // 50% of 180px
  squareBorderRadius: 8,
  glowSpread: 250,
} as const;

export const TIMING = {
  // Phase 1: Hold as blue circle (frames 0-5)
  holdStart: 0,
  holdEnd: 5,

  // Phase 2: Morph (frames 5-25)
  morphStart: 5,
  morphEnd: 25,
  glowPeak: 15,

  // Phase 3: Settle with overshoot (frames 25-33)
  settleStart: 25,
  settleEnd: 33,

  totalDuration: 33,
} as const;

export const MORPH = {
  breathingScale: 1.02,
  rotationDeg: 90,
  glowPeakOpacity: 0.25,
  overshootScale: 1.05,
} as const;

export const FPS = 30;
