export const CANVAS = {
  width: 1920,
  height: 1080,
} as const;

export const COLORS = {
  gradientTop: '#0f172a',
  gradientBottom: '#1e293b',
  titleWhite: '#ffffff',
  subtitleGray: '#94a3b8',
  accentBlue: '#3b82f6',
} as const;

export const TEXT = {
  title: 'ANIMATION SECTION',
  subtitle: 'Integration Test — Remotion Animations',
} as const;

export const DIMENSIONS = {
  titleFontSize: 96,
  subtitleFontSize: 32,
  accentLineWidth: 400,
  accentLineHeight: 4,
  accentLineY: 400,
  titleY: 440,
  subtitleY: 560,
} as const;

export const ANIMATION_TIMINGS = {
  backgroundFadeIn: { start: 0, end: 15 },
  accentLine: { start: 15, end: 30 },
  title: { start: 30, end: 45 },
  subtitle: { start: 45, end: 60 },
  particlesDuration: 90,
} as const;

export const PARTICLES = {
  count: 20,
  sizeMin: 2,
  sizeMax: 8,
  opacityMin: 0.2,
  opacityMax: 0.6,
} as const;
