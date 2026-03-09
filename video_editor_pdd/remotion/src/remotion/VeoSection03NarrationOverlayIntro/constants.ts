// Component-level constants for VeoSection03NarrationOverlayIntro

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: 'transparent',
  pillBackground: 'rgba(0, 0, 0, 0.55)',
  pillBorder: 'rgba(255, 255, 255, 0.1)',
  text: '#FFFFFF',
  progress: '#F59E0B',
  textShadow: 'rgba(0, 0, 0, 0.4)',
};

export const TYPOGRAPHY = {
  narration: {
    fontSize: 28,
    fontFamily: 'Inter',
    fontWeight: 500 as const,
    letterSpacing: '0.3px',
  },
};

export const POSITIONS = {
  pillY: 780,
};

export const DIMENSIONS = {
  pillPaddingH: 48,
  pillHeight: 64,
  pillBorderRadius: 16,
  blurRadius: 12,
  progressBarHeight: 3,
};

export const ANIMATION_TIMING = {
  // Pill fade in + slide up (frame 0-15)
  pillFadeInStart: 0,
  pillFadeInEnd: 15,
  pillSlideFrom: 800,
  pillSlideTo: 780,

  // Text fade in (frame 10-20)
  textFadeInStart: 10,
  textFadeInEnd: 20,

  // Progress bar fill (frame 15-75)
  progressStart: 15,
  progressEnd: 75,

  // Fade out (frame 75-90)
  fadeOutStart: 75,
  fadeOutEnd: 90,

  totalDuration: 90,
};

export const NARRATION_TEXT =
  'This is the second section of the integration test video.';
