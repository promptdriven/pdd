// Component-level constants for AnimationSection05SplitComparison
// Duration: 33 frames @ 30fps (~1.1s)

export const CANVAS = {
  width: 1280,
  height: 720,
} as const;

export const COLORS = {
  baseBg: '#141921',
  leftPanelBg: '#0F172A',
  rightPanelBg: '#0F2318',
  circle: '#3B82F6',
  square: '#22C55E',
  divider: '#FFFFFF',
  labelText: '#FFFFFF',
} as const;

export const DIMENSIONS = {
  circleDiameter: 120,
  squareSize: 110,
  squareBorderRadius: 6,
  dividerWidth: 2,
  dividerOpacity: 0.25,
  shapeCenterY: 320,
  labelY: 420,
  labelOpacity: 0.8,
} as const;

export const TYPOGRAPHY = {
  label: {
    fontSize: 24,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 500 as const,
  },
} as const;

export const ANIMATION_TIMING = {
  // Frame 0-8: Divider draws from center outward, panels tint in
  dividerDrawStart: 0,
  dividerDrawEnd: 8,
  // Frame 8-15: Shapes scale in with spring (circle at 8, square at 10)
  circleScaleStart: 8,
  squareScaleStart: 10,
  // Frame 15-20: Labels fade in (circle label at 15, square label at 17)
  circleLabelFadeStart: 15,
  squareLabelFadeStart: 17,
  labelFadeDuration: 5,
  // Frame 20-33: Breathing loop (15-frame sinusoidal cycle)
  breathingStart: 20,
  breathingCycleFrames: 15,
  breathingScaleMin: 1.0,
  breathingScaleMax: 1.04,
  totalDuration: 33,
} as const;

export const SHAPE_SPRING_CONFIG = {
  damping: 12,
  stiffness: 180,
  mass: 1,
} as const;
