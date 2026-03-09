// Component-level constants for AnimationSection01TitleCard

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0B1120',
  radialGlowCenter: '#1A2744',
  titleText: '#FFFFFF',
  accentLine: '#38BDF8',
};

export const TYPOGRAPHY = {
  title: {
    fontSize: 72,
    fontFamily: 'Inter',
    fontWeight: 'bold' as const,
    letterSpacing: '6px',
  },
};

export const DIMENSIONS = {
  accentLineHeight: 2,
  accentLineMaxWidth: 400,
  radialGlowDiameter: 600,
  titleToRuleGap: 16,
};

export const ANIMATION_TIMING = {
  // Frame 0-15: Background + radial glow fade in
  backgroundFadeStart: 0,
  backgroundFadeEnd: 15,
  // Frame 15-45: Title fade in with upward drift
  titleFadeStart: 15,
  titleFadeEnd: 45,
  // Frame 45-65: Horizontal rule expands
  ruleFadeStart: 45,
  ruleFadeEnd: 65,
  // Frame 65-90: Hold
  totalDuration: 90,
};
