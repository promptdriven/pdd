// Component-level constants for AnimationSection03CircleToSquareTransform

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#111827',
  circleBlue: '#FACC15',
  squareGreen: '#FACC15',
};

export const DIMENSIONS = {
  shapeWidth: 280,
  shapeHeight: 180,
  centerX: 960,
  centerY: 540,
  finalX: 1280,
  overshootX: 1300,
};

export const GHOST_TRAIL = {
  count: 3,
  opacities: [0.08, 0.05, 0.02],
  frameDelay: 2,
};

export const ANIMATION_TIMING = {
  // Frame 0-10: Hold — blue circle visible at center
  holdStart: 0,
  holdEnd: 10,
  // Frame 10-50: Morph — dimensions change circle→oval, color blue → green
  morphStart: 10,
  morphEnd: 50,
  // Frame 50-90: Slide — green oval moves from center to x=1280
  slideStart: 50,
  slideEnd: 90,
  // Frame 90-110: Settle — overshoot bounce to x=1300, ease back to x=1280
  settleStart: 90,
  settleEnd: 110,
  // Frame 110-150: Hold — yellow square at final position
  finalHoldStart: 110,
  totalDuration: 150,
};
