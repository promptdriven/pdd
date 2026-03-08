export const COLORS = {
  background: '#0F172A',
  heading: '#F8FAFC',
  label: '#E2E8F0',
  skyBlue: '#38BDF8',
  green: '#22C55E',
  barShadow: 'rgba(15, 23, 42, 0.45)',
};

export const DIMENSIONS = {
  canvasWidth: 1920,
  canvasHeight: 1080,
  barWidth: 120,
  maxBarHeight: 360,
  barGap: 36,
  barRadius: 24,
  baseline: 750,
};

export const BARS = [
  { label: 'Metric A', value: 0.35, color: COLORS.skyBlue, percentLabel: '35%' },
  { label: 'Metric B', value: 0.55, color: COLORS.green, percentLabel: '55%' },
  { label: 'Metric C', value: 0.80, color: COLORS.skyBlue, percentLabel: '80%' },
  { label: 'Metric D', value: 0.60, color: COLORS.green, percentLabel: '60%' },
];

export const TIMING = {
  barStaggerDelay: 10,
  barGrowDuration: 20,
  labelFadeStart: 50,
  labelStaggerDelay: 5,
  labelFadeDuration: 15,
  totalFrames: 75,
};

export const TYPOGRAPHY = {
  headingSize: 52,
  headingWeight: 700 as const,
  headingX: 72,
  headingY: 72,
  labelSize: 24,
  labelWeight: 700 as const,
  fontFamily: 'Inter, sans-serif',
};
