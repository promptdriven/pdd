export const COLORS = {
  background: '#0A1628',
  heading: '#F8FAFC',
  cyan: '#38BDF8',
  green: '#22C55E',
  barShadow: 'rgba(15, 23, 42, 0.45)',
};

export const DIMENSIONS = {
  canvasWidth: 1920,
  canvasHeight: 1080,
  barWidth: 120,
  barGap: 36,
  containerHeight: 420,
  barBaseHeight: 360,
  barRadius: 24,
};

export const BARS = [
  { value: 0.35, maxHeight: 126, color: COLORS.cyan },
  { value: 0.55, maxHeight: 198, color: COLORS.green },
  { value: 0.80, maxHeight: 288, color: COLORS.cyan },
  { value: 0.60, maxHeight: 216, color: COLORS.green },
];

export const TIMING = {
  barGrowDuration: 20,
  barStaggerDelay: 10,
};

export const TYPOGRAPHY = {
  headingSize: 52,
  headingWeight: 700 as const,
  headingX: 72,
  headingY: 72,
  fontFamily: 'Inter, sans-serif',
};
