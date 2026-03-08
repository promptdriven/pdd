// Component-level constants for AnimationSection08SectionClosingCard

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  gradientTop: '#0A1628',
  gradientBottom: '#1E3A8A',
  checkmark: '#22C55E',
  taglineText: '#94A3B8',
  rule: '#3B82F6',
  particleColor: '#3B82F6',
};

export const TYPOGRAPHY = {
  tagline: {
    fontSize: 36,
    fontFamily: 'Inter',
    fontWeight: 400 as const,
    letterSpacing: '2px',
    textTransform: 'uppercase' as const,
  },
};

export const POSITIONS = {
  checkmarkCy: 440,
  taglineY: 540,
  ruleY: 590,
};

export const DIMENSIONS = {
  checkmarkRadius: 32,
  checkmarkStrokeWidth: 3,
  ruleMaxWidth: 200,
  ruleHeight: 2,
};

export const ANIMATION_TIMING = {
  // Background fade: frames 0-10
  bgFadeStart: 0,
  bgFadeEnd: 10,
  // Checkmark draw: frames 5-25
  checkmarkStart: 5,
  checkmarkEnd: 25,
  // Tagline fade: frames 15-30
  taglineFadeStart: 15,
  taglineFadeEnd: 30,
  // Rule expand: frames 25-40
  ruleExpandStart: 25,
  ruleExpandEnd: 40,
  // Card fade-out: frames 35-45
  cardFadeOutStart: 35,
  cardFadeOutEnd: 45,
  totalDuration: 45,
};

export const PARTICLES = {
  count: 20,
  speed: 1,
  minSize: 2,
  maxSize: 5,
  color: COLORS.particleColor,
  opacityMin: 0.1,
  opacityMax: 0.3,
};
