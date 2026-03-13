// Component-level constants for AnimationSection01TitleCard
// Duration: ~1.5s (45 frames @ 30fps)

export const CANVAS = {
  width: 1920,
  height: 1080,
} as const;

export const COLORS = {
  background: '#0F172A',
  titleWhite: '#FFFFFF',
  subtitleSlate: '#CBD5E1',
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

export const DIMENSIONS = {
  titleOffsetY: -40,
  accentLineEndWidth: 400,
  accentLineHeight: 2,
  accentLineGap: 16,
  subtitleGap: 24,
} as const;

export const ANIMATION_TIMING = {
  // Frame 0-15: Title fades in opacity 0->1, scales 0.95->1.0
  titleFadeStart: 0,
  titleFadeEnd: 15,
  titleScaleStart: 0.95,
  titleScaleEnd: 1.0,
  // Frame 9-24: Accent line expands from 0->400px
  accentLineStart: 9,
  accentLineEnd: 24,
  // Frame 15-30: Subtitle fades in opacity 0->1
  subtitleFadeStart: 15,
  subtitleFadeEnd: 30,
  // Frame 30-45: Hold
  totalDuration: 45,
} as const;
