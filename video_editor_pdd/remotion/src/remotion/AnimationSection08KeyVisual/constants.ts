export const COLORS = {
  background: '#0A1628',
  cyan: '#38BDF8',
  green: '#22C55E',
  white: '#FFFFFF',
  gridLine: 'rgba(255, 255, 255, 0.05)',
  barShadow: 'rgba(0, 0, 0, 0.3)',
};

export const BARS = [
  { height: 300, color: COLORS.cyan, label: 'A' },
  { height: 420, color: COLORS.green, label: 'B' },
  { height: 260, color: COLORS.cyan, label: 'C' },
  { height: 500, color: COLORS.green, label: 'D' },
];

export const DIMENSIONS = {
  canvasWidth: 1920,
  canvasHeight: 1080,
  barWidth: 120,
  barGap: 30,
  maxHeight: 500,
  containerWidth: 600,
  containerBottomY: 880,
  barBorderRadius: '8px 8px 0 0',
};

export const TIMING = {
  labelFadeStart: 0,
  labelFadeEnd: 4,
  barGrowFrames: 8,
  barStaggerFrames: 3,
  pulseStart: 19,
  totalFrames: 24,
};

export const TYPOGRAPHY = {
  fontFamily: 'Inter, sans-serif',
  labelSize: 20,
  labelWeight: 600 as const,
  labelX: 80,
  labelY: 60,
  labelOpacity: 0.7,
};
