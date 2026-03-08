/**
 * Component-level constants for AnimationSection02AnimatedBarChart
 */

export const COLORS = {
  background: '#ffffff',
  gridLine: '#e2e8f0',
  axisLabel: '#64748b',
  categoryLabel: '#1e293b',
  alpha: '#3b82f6',
  beta: '#8b5cf6',
  gamma: '#ec4899',
  delta: '#10b981',
} as const;

export const DIMENSIONS = {
  chartWidth: 1200,
  chartHeight: 600,
  barWidth: 120,
  barGap: 140,
  borderRadius: 8,
  valueLabelOffset: 12,
} as const;

export const TYPOGRAPHY = {
  axisLabelSize: 16,
  categoryLabelSize: 20,
  valueLabelSize: 24,
  fontFamily: 'Inter',
} as const;

export const CHART_DATA = [
  { category: 'Alpha', value: 75, color: COLORS.alpha },
  { category: 'Beta', value: 92, color: COLORS.beta },
  { category: 'Gamma', value: 58, color: COLORS.gamma },
  { category: 'Delta', value: 85, color: COLORS.delta },
] as const;

export const MAX_VALUE = 100;
export const GRID_LINES = 5;
export const STAGGER_DELAY = 5;

export const TIMING = {
  gridFadeStart: 0,
  gridFadeDuration: 15,
  barsStart: 15,
  barsDuration: 30,
  labelsStart: 45,
  labelsDuration: 15,
  holdStart: 60,
  totalDuration: 120,
} as const;
