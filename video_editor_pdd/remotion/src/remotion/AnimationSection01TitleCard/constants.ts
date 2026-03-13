// Component-level constants for AnimationSection01TitleCard
// Duration: ~1.1s (33 frames @ 30fps)

export const CANVAS = {
  width: 1280,
  height: 720,
};

export const COLORS = {
  background: '#0B1120',
  glowCenter: '#2E4A7A',
  titleText: '#FFFFFF',
  divider: 'rgba(255,255,255,0.4)',
};

export const TYPOGRAPHY = {
  title: {
    fontFamily: "'Inter', sans-serif",
    fontSize: 56,
    fontWeight: 700 as const,
    letterSpacing: 2,
  },
};

export const DIMENSIONS = {
  glowInitialRadius: 300,
  glowExpandedRadius: 400,
  glowPulseRadius: 500,
  glowRestingRadius: 400,
  glowInitialOpacity: 0,
  glowExpandedOpacity: 0.4,
  glowPulseOpacity: 0.5,
  glowRestingOpacity: 0.35,
  titleOffsetY: -20,
  dividerWidth: 200,
  dividerHeight: 2,
  dividerOffsetY: 40,
  floatAmplitude: 2,
  letterTranslateY: 8,
};

export const ANIMATION_TIMING = {
  // Frame 0-5: Background fades in from black, glow begins expanding
  backgroundFadeStart: 0,
  backgroundFadeEnd: 5,
  // Frame 5-20: Title text staggers in letter-by-letter
  titleStaggerStart: 5,
  framesPerChar: 1.5,
  // Frame 20-25: Divider expands, glow pulses
  dividerExpandStart: 20,
  dividerExpandEnd: 25,
  glowPulseStart: 20,
  glowPulseEnd: 25,
  // Frame 25-33: Hold with gentle float
  holdStart: 25,
  totalDuration: 33,
};

export const TITLE_TEXT = 'Animation Section';
