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
  { value: 0.60, maxHeight: 300, color: COLORS.cyan },
  { value: 0.84, maxHeight: 420, color: COLORS.green },
  { value: 0.52, maxHeight: 260, color: COLORS.cyan },
  { value: 1.0, maxHeight: 500, color: COLORS.green },
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
