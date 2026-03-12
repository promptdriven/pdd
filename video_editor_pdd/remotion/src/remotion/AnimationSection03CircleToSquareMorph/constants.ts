// Component-level constants for AnimationSection03CircleToSquareMorph

export const CANVAS = {
  width: 1280,
  height: 720,
};

export const COLORS = {
  background: '#141921',
  fromShape: '#3B82F6',
  toShape: '#22C55E',
};

export const DIMENSIONS = {
  fromSize: 180,
  toSize: 160,
  glowBlur: 25,
};

export const TIMING = {
  // Phase 1 (0-15): Hold as blue circle with subtle breathing
  holdStart: 0,
  holdEnd: 15,
  // Phase 2 (15-60): Morph — border-radius, color, rotation, size
  morphStart: 15,
  morphEnd: 60,
  // Phase 3 (60-90): Settle — scale overshoot + glow stabilize
  settleStart: 60,
  totalDuration: 90,
};

export const MORPH = {
  rotationDegrees: 90,
  breathingScale: 1.02,
  settleOvershootScale: 1.05,
  glowOpacityMorph: 0.25,
  glowOpacitySettle: 0.2,
};

export const FPS = 30;
