// Component-level constants for VeoSection01TitleCard

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  gradientTop: '#0A1A1F',
  gradientBottom: '#0F2027',
  titleText: '#F8FAFC',
  accentLine: '#D4A574',
  bokehWarm1: '#D4A574',
  bokehWarm2: '#F59E0B',
  filmGrain: '#FFFFFF',
};

export const TYPOGRAPHY = {
  title: {
    fontSize: 64,
    fontFamily: 'Inter',
    fontWeight: 'bold' as const,
    letterSpacing: '-1px',
  },
};

export const POSITIONS = {
  titleY: 460,
  accentLineY: 520,
};

export const DIMENSIONS = {
  accentLineHeight: 2,
  accentLineWidth: 350,
};

export const ANIMATION_TIMING = {
  backgroundFadeStart: 0,
  backgroundFadeEnd: 12,
  titleFadeStart: 12,
  titleFadeEnd: 32,
  ruleFadeStart: 22,
  ruleFadeEnd: 42,
  totalDuration: 60,
};

export const BOKEH = {
  count: 20,
  minRadius: 6,
  maxRadius: 18,
  driftSpeed: 0.4,
};
