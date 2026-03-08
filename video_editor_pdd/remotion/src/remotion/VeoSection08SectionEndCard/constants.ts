// Component-level constants for VeoSection08SectionEndCard

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  gradientTop: '#0A1A1F',
  gradientBottom: '#0F2027',
  accentWarm: '#D4A574',
  accentGold: '#F59E0B',
  titleText: '#F8FAFC',
  subtitleText: '#94A3B8',
  ruleColor: '#D4A574',
  particleColor1: '#D4A574',
  particleColor2: '#F59E0B',
  ringStroke: '#D4A574',
  filmGrain: '#FFFFFF',
};

export const TYPOGRAPHY = {
  title: {
    fontSize: 48,
    fontFamily: 'Inter',
    fontWeight: 700 as const,
    letterSpacing: '-0.5px',
  },
  subtitle: {
    fontSize: 28,
    fontFamily: 'Inter',
    fontWeight: 400 as const,
    letterSpacing: '3px',
    textTransform: 'uppercase' as const,
  },
};

export const POSITIONS = {
  ringCy: 400,
  titleY: 510,
  subtitleY: 580,
  ruleY: 640,
};

export const DIMENSIONS = {
  ringRadius: 48,
  ringStrokeWidth: 2.5,
  checkSize: 28,
  ruleMaxWidth: 280,
  ruleHeight: 1.5,
};

export const ANIMATION_TIMING = {
  // Ring draw: frames 0-20
  ringDrawStart: 0,
  ringDrawEnd: 20,
  // Checkmark draw: frames 12-28
  checkmarkStart: 12,
  checkmarkEnd: 28,
  // Title fade: frames 18-32
  titleFadeStart: 18,
  titleFadeEnd: 32,
  // Subtitle fade: frames 26-38
  subtitleFadeStart: 26,
  subtitleFadeEnd: 38,
  // Rule expand: frames 32-44
  ruleExpandStart: 32,
  ruleExpandEnd: 44,
  // Card fade-out: frames 48-60
  cardFadeOutStart: 48,
  cardFadeOutEnd: 60,
  totalDuration: 60,
};

export const PARTICLES = {
  count: 18,
  minRadius: 4,
  maxRadius: 14,
  driftSpeed: 0.3,
  opacityMin: 0.05,
  opacityMax: 0.2,
};
