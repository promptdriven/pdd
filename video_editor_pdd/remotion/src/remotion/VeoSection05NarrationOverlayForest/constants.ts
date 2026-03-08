// Component-level constants for VeoSection05NarrationOverlayForest

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: 'transparent',
  pillBackground: 'rgba(0, 0, 0, 0.55)',
  pillBorder: 'rgba(255, 255, 255, 0.12)',
  text: '#FFFFFF',
  accent: '#34D399',
  accentGlow: 'rgba(52, 211, 153, 0.6)',
  textShadow: 'rgba(0, 0, 0, 0.4)',
};

export const TYPOGRAPHY = {
  subtitle: {
    fontSize: 28,
    fontFamily: 'Inter',
    fontWeight: 500 as const,
    letterSpacing: '0.3px',
  },
};

export const POSITIONS = {
  pillY: 920,
};

export const DIMENSIONS = {
  pillWidth: 900,
  pillHeight: 72,
  pillBorderRadius: 36,
  accentBarWidth: 4,
  accentBarHeight: 48,
  accentBarInset: 16,
  blurRadius: 12,
};

export const ANIMATION_TIMING = {
  // Pill slide in from right
  slideInStart: 0,
  slideInEnd: 15,
  slideDistance: 200,

  // Accent bar scale in
  accentBarStart: 10,
  accentBarEnd: 20,

  // Text clip-path reveal
  textRevealStart: 12,
  textRevealEnd: 55,

  // Hold
  holdEnd: 75,

  // Pill slide out to left
  slideOutStart: 75,
  slideOutEnd: 90,
  slideOutDistance: 200,

  totalDuration: 90,
};

export const NARRATION_TEXT =
  'It uses Veo-generated clips with narration overlay.';
