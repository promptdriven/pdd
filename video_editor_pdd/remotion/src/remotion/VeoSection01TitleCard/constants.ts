// Component-level constants for VeoSection01TitleCard

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#121212',
  gradientCenter: '#2A1F0E',
  titleText: '#FFF8E7',
  accent: '#F59E0B',
  glowColor: '#2A1F0E',
  filmGrain: '#FFFFFF',
};

export const TYPOGRAPHY = {
  title: {
    fontSize: 72,
    fontFamily: 'Inter',
    fontWeight: 'bold' as const,
    letterSpacing: 8,
  },
};

export const ANIMATION = {
  backgroundFadeStart: 0,
  backgroundFadeEnd: 10,
  lightStreakStart: 10,
  lightStreakEnd: 30,
  letterRevealStart: 15,
  letterStaggerFrames: 2,
  glowPulseStart: 30,
  glowPulseEnd: 50,
  holdStart: 50,
  totalDuration: 90,
};

export const DIMENSIONS = {
  glowDiameter: 500,
  lightStreakHeight: 1,
  grainOpacity: 0.03,
};
