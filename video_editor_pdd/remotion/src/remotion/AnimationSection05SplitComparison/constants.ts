// Component-level constants for AnimationSection05SplitComparison

export const CANVAS = {
  width: 1280,
  height: 720,
};

export const COLORS = {
  leftPanelBg: '#0F172A',
  rightPanelBg: '#0F2318',
  circle: '#3B82F6',
  square: '#22C55E',
  divider: '#FFFFFF',
  labelText: '#FFFFFF',
};

export const DIMENSIONS = {
  circleDiameter: 120,
  squareSize: 110,
  dividerWidth: 2,
  dividerOpacity: 0.25,
  shapeCenterY: 320,
  labelY: 440,
  labelOpacity: 0.7,
};

export const TYPOGRAPHY = {
  label: {
    fontSize: 24,
    fontFamily: 'Inter',
    fontWeight: 500 as const,
  },
};

export const ANIMATION_TIMING = {
  // Frame 0-20: Divider draws from center outward, panels tint in
  dividerDrawStart: 0,
  dividerDrawEnd: 20,
  // Frame 20-40: Shapes scale in (circle at 20, square at 25)
  circleScaleStart: 20,
  squareScaleStart: 25,
  // Frame 40-55: Labels fade in
  labelFadeStart: 40,
  labelFadeEnd: 55,
  // Frame 55-90: Breathing loop (30-frame cycle)
  breathingStart: 55,
  breathingCycleFrames: 30,
  breathingScaleMin: 1.0,
  breathingScaleMax: 1.04,
  totalDuration: 90,
};

// Spring config for shape scale-in
export const SHAPE_SPRING_CONFIG = {
  damping: 12,
  stiffness: 180,
  mass: 1,
};
