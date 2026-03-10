// Component-level constants for AnimationSection04CircleToSquareTransform

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0F172A',
  shapeStart: '#EC4899',
  shapeEnd: '#22C55E',
};

export const SHAPE = {
  size: 160,
  startBorderRadius: 80,
  endBorderRadius: 12,
  startX: 960,
  endX: 1400,
  cy: 540,
};

export const TRAIL = {
  count: 4,
  spacing: 60,
  opacities: [0.15, 0.10, 0.06, 0.03],
};

export const GLOW = {
  blur: 40,
  opacity: 0.2,
};

export const TIMING = {
  // Border-radius morph: frames 0-20
  morphStart: 0,
  morphEnd: 20,
  // Color transition: frames 10-30
  colorStart: 10,
  colorEnd: 30,
  // Horizontal slide: frames 20-55
  slideStart: 20,
  slideEnd: 55,
  // Settle bounce: frames 55-75
  settleStart: 55,
  settleEnd: 75,
  // Total
  totalDuration: 75,
};
