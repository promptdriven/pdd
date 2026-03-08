// Component-level constants for VeoSection03NarrationOverlayIntro

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0A1628',
  gradientFrom: 'transparent',
  gradientTo: '#00000090',
  text: '#FFFFFF',
  accent: '#D4A574',
};

export const TYPOGRAPHY = {
  subtitle: {
    fontSize: 32,
    fontFamily: 'Inter',
    fontWeight: 'normal' as const,
    letterSpacing: '0.5px',
  },
};

export const POSITIONS = {
  textY: 920,
  accentLineY: 885,
};

export const DIMENSIONS = {
  gradientBarHeight: 160,
  accentLineWidth: 60,
  accentLineHeight: 3,
  textMaxWidth: 1400,
  textPadding: 20,
};

export const ANIMATION_TIMING = {
  // Gradient bar fade in
  gradientFadeStart: 0,
  gradientFadeEnd: 10,

  // Accent line scale in + text begins
  accentLineStart: 8,
  accentLineEnd: 18,

  // Text type-on
  typeOnStart: 10,
  typeOnEnd: 60,

  // Hold
  holdEnd: 80,

  // Fade out
  fadeOutStart: 80,
  fadeOutEnd: 90,

  totalDuration: 90,
};

export const NARRATION_TEXT =
  'This is the second section of the integration test video.';

export const TYPE_SPEED = 1.5; // chars per frame
