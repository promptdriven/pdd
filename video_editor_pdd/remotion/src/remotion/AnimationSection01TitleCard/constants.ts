// Component-level constants for AnimationSection01TitleCard

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  gradientTop: '#0A1628',
  gradientBottom: '#1E3A8A',
  titleText: '#FFFFFF',
  subtitleText: '#94A3B8',
  accentLine: '#3B82F6',
  particleColor: '#3B82F6',
};

export const TYPOGRAPHY = {
  title: {
    fontSize: 96,
    fontFamily: 'Inter',
    fontWeight: 'bold' as const,
    letterSpacing: '-2px',
  },
  subtitle: {
    fontSize: 32,
    fontFamily: 'Inter',
    fontWeight: 'normal' as const,
    letterSpacing: '0px',
  },
};

export const POSITIONS = {
  titleY: 460,
  subtitleY: 580,
  titleStartY: 500,
};

export const DIMENSIONS = {
  accentLineHeight: 4,
  accentLineWidth: 400,
  glowBlurRadius: 40,
};

export const ANIMATION_TIMING = {
  backgroundFadeStart: 0,
  backgroundFadeEnd: 15,
  titleSlideStart: 15,
  titleSlideEnd: 45,
  accentLineStart: 30,
  accentLineEnd: 60,
  subtitleFadeStart: 45,
  subtitleFadeEnd: 75,
  totalDuration: 90,
};

export const PARTICLES = {
  count: 60,
  speed: 2,
  minSize: 2,
  maxSize: 6,
  color: COLORS.particleColor,
};
