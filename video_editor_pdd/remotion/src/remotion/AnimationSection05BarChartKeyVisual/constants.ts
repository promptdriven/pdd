// Component-level constants for AnimationSection05BarChartKeyVisual

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0F172A',
  skyBlue: '#38BDF8',
  emeraldGreen: '#22C55E',
  headingText: '#F8FAFC',
  labelText: '#E2E8F0',
};

export const BARS = [
  { label: 'Metric A', value: 0.35, color: COLORS.skyBlue },
  { label: 'Metric B', value: 0.55, color: COLORS.emeraldGreen },
  { label: 'Metric C', value: 0.80, color: COLORS.skyBlue },
  { label: 'Metric D', value: 0.60, color: COLORS.emeraldGreen },
] as const;

export const CHART = {
  barWidth: 120,
  maxBarHeight: 360,
  gap: 36,
  borderRadius: 24,
  baselineY: 750,
  staggerDelayFrames: 10,
  barGrowDuration: 20,
};

export const TYPOGRAPHY = {
  heading: {
    fontSize: 52,
    fontFamily: 'Inter',
    fontWeight: 700 as const,
  },
  label: {
    fontSize: 24,
    fontFamily: 'Inter',
    fontWeight: 700 as const,
  },
};

export const POSITIONS = {
  headingX: 72,
  headingY: 72,
};

export const ANIMATION_TIMING = {
  labelFadeStart: 50,
  labelStagger: 5,
  labelFadeDuration: 15,
  totalDuration: 75,
};

export const SPRING_CONFIG = {
  damping: 12,
  stiffness: 100,
  mass: 1,
};
