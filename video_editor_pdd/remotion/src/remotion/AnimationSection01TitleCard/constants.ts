// Component-level constants for AnimationSection01TitleCard

export const CANVAS = {
  width: 1280,
  height: 720,
};

export const COLORS = {
  background: '#0B1120',
  glowCenter: '#2E4A7A',
  gradientCenter: '#1A2744',
  titleText: '#FFFFFF',
  divider: '#FFFFFF',
};

export const TYPOGRAPHY = {
  title: {
    fontSize: 56,
    fontFamily: 'Inter',
    fontWeight: 'bold' as const,
  },
};

export const DIMENSIONS = {
  dividerWidth: 200,
  dividerHeight: 2,
  dividerOpacity: 0.4,
  dividerOffsetY: 20,
  glowRadius: 300,
  glowBaseOpacity: 0.3,
  glowPulseOpacity: 0.5,
  floatAmplitude: 2,
};

export const ANIMATION_TIMING = {
  // Frame 0-15: Background fades in, glow expands
  backgroundFadeStart: 0,
  backgroundFadeEnd: 15,
  // Frame 15-45: Title letter-by-letter stagger
  titleStaggerStart: 15,
  titleStaggerEnd: 45,
  letterStaggerFrames: 1.5, // ~50ms per char at 30fps
  letterTranslateY: 5,
  // Frame 45-60: Divider expands, glow pulses
  dividerExpandStart: 45,
  dividerExpandEnd: 60,
  glowPulseStart: 45,
  glowPulseEnd: 60,
  // Frame 60-90: Hold with float
  holdStart: 60,
  totalDuration: 90,
};

export const TITLE_TEXT = 'Animation Section';
