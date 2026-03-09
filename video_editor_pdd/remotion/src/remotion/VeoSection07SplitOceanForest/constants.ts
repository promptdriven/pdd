// Component-level constants for VeoSection07SplitOceanForest
// Split-screen comparison: ocean wave sunset vs forest canopy aerial

export const CANVAS = {
  width: 1920,
  height: 1080,
  dividerX: 960,
};

export const COLORS = {
  background: '#000000',
  divider: 'rgba(255, 255, 255, 0.8)',
  dividerGlow: 'rgba(245, 158, 11, 0.2)',
  label: 'rgba(255, 255, 255, 0.9)',
};

export const TYPOGRAPHY = {
  label: {
    fontSize: 16,
    fontFamily: 'Inter',
    fontWeight: 600 as const,
    letterSpacing: '2px',
  },
};

export const POSITIONS = {
  leftPanelRestX: 0,
  rightPanelRestX: 972,
  leftLabelX: 40,
  rightLabelX: 1680,
  labelY: 1020,
};

export const DIMENSIONS = {
  panelWidth: 948,
  panelHeight: 1080,
  dividerWidth: 4,
  dividerGlowWidth: 24,
  gap: 24, // gap between panels (972 - 948 = 24)
};

export const ANIMATION = {
  // Frame 0-20: Panels slide apart from center overlap
  panelSlideStart: 0,
  panelSlideEnd: 20,

  // Frame 0-20: Divider fades in
  dividerFadeStart: 5,
  dividerFadeEnd: 20,

  // Frame 20-30: Labels fade in with upward drift
  labelFadeInStart: 20,
  labelFadeInEnd: 30,

  // Frame 30-75: Hold
  // Frame 75-90: Labels fade out
  labelFadeOutStart: 75,
  labelFadeOutEnd: 90,

  totalDuration: 90,
};

export const LABELS = {
  left: 'OCEAN — SUNSET',
  right: 'FOREST — AERIAL',
};
