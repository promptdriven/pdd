// Component-level constants for AnimationSection04SquareSlideRight

export const CANVAS = {
  width: 1280,
  height: 720,
};

export const COLORS = {
  background: '#141921',
  square: '#22C55E',
  guideLine: '#FFFFFF',
  glowColor: '#22C55E',
};

export const DIMENSIONS = {
  squareSize: 160,
  startX: 640,
  endX: 920,
  overshootX: 935,
  centerY: 360,
  trailCount: 4,
  trailSpacing: 40,
  trailDelayFrames: 3,
  trailOpacities: [0.15, 0.10, 0.06, 0.03],
  guideLineOpacity: 0.1,
  guideLineWidth: 1,
  glowSize: 240,
  glowOpacity: 0.3,
};

export const ANIMATION_TIMING = {
  // Phase 1: Frame 0-10 — hold at center, guide line fades in
  holdEnd: 10,
  guideFadeInStart: 0,
  guideFadeInEnd: 10,
  // Phase 2: Frame 10-60 — slide right with trail
  slideStart: 10,
  slideEnd: 60,
  // Phase 3: Frame 60-75 — overshoot settle
  settleStart: 60,
  settleEnd: 75,
  // Phase 4: Frame 75-90 — rest, guide fades out, glow appears
  guideFadeOutStart: 75,
  guideFadeOutEnd: 90,
  glowFadeInStart: 75,
  glowFadeInEnd: 90,
  totalDuration: 90,
};
