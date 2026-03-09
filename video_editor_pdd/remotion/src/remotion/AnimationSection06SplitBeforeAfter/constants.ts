// Component-level constants for AnimationSection06SplitBeforeAfter

export const CANVAS = {
  width: 1920,
  height: 1080,
  dividerX: 960,
};

export const COLORS = {
  backgroundLeft: '#111827',
  backgroundRight: '#0F172A',
  divider: '#F8FAFC',
  circle: '#3B82F6',
  square: '#22C55E',
  label: '#F8FAFC',
};

export const TYPOGRAPHY = {
  label: {
    fontSize: 28,
    fontFamily: 'Inter',
    fontWeight: 'bold' as const,
    letterSpacing: '4px',
  },
};

export const POSITIONS = {
  leftCenterX: 480,
  rightCenterX: 480,
  centerY: 540,
  labelY: 80,
};

export const DIMENSIONS = {
  shapeSize: 160,
  dividerWidth: 3,
  vignetteSize: 40,
};

export const ANIMATION_TIMING = {
  // Frame 0-15: Divider slides down from top
  dividerStart: 0,
  dividerEnd: 15,
  // Frame 15-40: Left panel fades in (circle + BEFORE label)
  leftPanelStart: 15,
  leftPanelEnd: 40,
  // Frame 20-45: Right panel fades in (square + AFTER label)
  rightPanelStart: 20,
  rightPanelEnd: 45,
  // Frame 45-120: Hold
  totalDuration: 120,
};
