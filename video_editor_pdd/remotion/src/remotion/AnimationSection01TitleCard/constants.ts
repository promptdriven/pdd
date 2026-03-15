// Component-level constants for AnimationSection01TitleCard
// Duration: ~1.5s (45 frames @ 30fps)

export const CANVAS = {
  width: 1920,
  height: 1080,
} as const;

export const COLORS = {
  background: '#0F172A',
  titleWhite: '#FFFFFF',
  subtitleSlate: '#94A3B8',
  accentLine: 'rgba(255, 255, 255, 0.8)',
} as const;

export const TEXT = {
  title: 'Animation Section',
  subtitle: 'Integration Test',
} as const;

export const TYPOGRAPHY = {
  title: {
    fontFamily: "'Inter', sans-serif",
    fontSize: 72,
    fontWeight: 700 as const,
  },
  subtitle: {
    fontFamily: "'Inter', sans-serif",
    fontSize: 28,
    fontWeight: 400 as const,
  },
} as const;

export const POSITIONS = {
  titleY: 440,
  accentLineY: 500,
  subtitleY: 560,
  subtitleDrift: 10,
} as const;

export const DIMENSIONS = {
  accentLineEndWidth: 320,
  accentLineHeight: 2,
} as const;

export const ANIMATION_TIMING = {
  // Frame 0-15: Title fades in opacity 0->1, scales 0.85->1.0
  titleFadeStart: 0,
  titleFadeEnd: 15,
  titleScaleStart: 0.85,
  titleScaleEnd: 1.0,
  // Frame 12-30: Accent line expands from 0->320px
  accentLineStart: 12,
  accentLineEnd: 30,
  // Frame 20-40: Subtitle fades in opacity 0->1 with 10px upward drift
  subtitleFadeStart: 20,
  subtitleFadeEnd: 40,
  // Frame 40-45: Hold
  totalDuration: 45,
} as const;
