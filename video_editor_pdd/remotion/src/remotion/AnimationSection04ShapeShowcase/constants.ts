// Component-level constants for AnimationSection04ShapeShowcase

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0F172A',
  cardBackground: '#1E293B',
  cardBorder: '#334155',
  circleBlue: '#3B82F6',
  squareGreen: '#22C55E',
  subtitleText: '#94A3B8',
  labelText: '#E2E8F0',
  arrowStroke: '#475569',
};

export const TYPOGRAPHY = {
  subtitle: {
    fontSize: 36,
    fontFamily: 'Inter',
    fontWeight: 600 as const,
    letterSpacing: '1px',
  },
  label: {
    fontSize: 24,
    fontFamily: 'Inter',
    fontWeight: 500 as const,
  },
};

export const DIMENSIONS = {
  cardSize: 360,
  cardBorderRadius: 16,
  shapeSize: 120,
  leftCardCenterX: 560,
  rightCardCenterX: 1360,
  cardCenterY: 440,
  arrowStartX: 740,
  arrowEndX: 1180,
  arrowY: 440,
  subtitleY: 140,
};

export const ANIMATION_TIMING = {
  // Frame 0-20: Subtitle fades in from above
  subtitleFadeStart: 0,
  subtitleFadeEnd: 20,
  // Frame 20-50: Left card slides in, circle scales
  leftCardStart: 20,
  leftCardEnd: 50,
  // Frame 40-70: Right card slides in, square scales
  rightCardStart: 40,
  rightCardEnd: 70,
  // Frame 60-80: Dotted arrow draws
  arrowDrawStart: 60,
  arrowDrawEnd: 80,
  // Frame 80-100: Labels fade in
  labelFadeStart: 80,
  labelFadeEnd: 100,
  // Total duration
  totalDuration: 150,
};
