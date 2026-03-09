// Component-level constants for AnimationSection07SectionClosingCard

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0B1120',
  titleText: '#F1F5F9',
  accentCyan: '#38BDF8',
  circleBlue: '#3B82F6',
  squareGreen: '#22C55E',
  particleColor: '#38BDF8',
};

export const TYPOGRAPHY = {
  title: {
    fontSize: 48,
    fontFamily: 'Inter',
    fontWeight: 'bold' as const,
    letterSpacing: '4px',
  },
};

export const DIMENSIONS = {
  ruleWidth: 300,
  ruleHeight: 2,
  ruleY: 420,
  textY: 500,
  shapesY: 620,
  circleRadius: 24,
  squareSize: 48,
  circleX: 920,
  squareX: 1000,
  particleSize: 4,
  particleCount: 8,
};

export const ANIMATION_TIMING = {
  // Frame 0-15: Rule expands from center, background fades in
  ruleExpandStart: 0,
  ruleExpandEnd: 15,
  backgroundFadeStart: 0,
  backgroundFadeEnd: 15,
  // Frame 15-35: Text fades in
  textFadeStart: 15,
  textFadeEnd: 35,
  // Frame 30-45: Shapes pop in (circle at 30, square at 34)
  circlePopStart: 30,
  circlePopEnd: 45,
  squarePopStart: 34,
  squarePopEnd: 49,
  // Frame 45-65: Hold
  // Frame 65-90: Fade out everything
  fadeOutStart: 65,
  fadeOutEnd: 90,
  totalDuration: 90,
};
