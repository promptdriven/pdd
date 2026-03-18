// Color palette
export const COLORS = {
  background: '#0A0F1A',
  axisLine: '#334155',
  axisLabel: '#64748B',
  title: '#E2E8F0',
  curve: '#4A90D9',
  curveGlow: 'rgba(74,144,217,0.15)',
  curveFillTop: 'rgba(74,144,217,0.05)',
  leftZone: '#D9944A',
  rightZone: '#5AAA6E',
  slider: '#E2E8F0',
  sliderGlow: 'rgba(74,144,217,0.3)',
  promptLines: 'rgba(74,144,217,0.5)',
  wallIcon: 'rgba(217,148,74,0.5)',
} as const;

// Layout
export const CANVAS = { width: 1920, height: 1080 } as const;

export const CHART = {
  originX: 260,
  originY: 820,
  endX: 1620,
  topY: 180,
  width: 1360,
  height: 640,
} as const;

// Timing (frames at 30fps)
export const TIMING = {
  axesDrawStart: 0,
  axesDrawEnd: 30,
  ticksStart: 30,
  ticksEnd: 60,
  curveStart: 60,
  curveEnd: 180,
  leftZoneStart: 180,
  leftZoneEnd: 210,
  rightZoneStart: 240,
  rightZoneEnd: 270,
  sliderStart: 300,
  sliderEnd: 390,
  holdStart: 390,
  totalFrames: 450,
} as const;

// X-axis ticks
export const X_TICKS = [0, 10, 20, 30, 40, 50] as const;
export const Y_TICK_LABELS = ['Low', 'Medium', 'High'] as const;

// Curve function: maps testCount (0-50) to pixel Y
export function curveY(testCount: number): number {
  return CHART.topY + (CHART.height - (CHART.topY - CHART.topY)) * (1 / (1 + 0.08 * testCount));
}

// More precise: maps testCount to pixel coords
export function curvePoint(testCount: number): { x: number; y: number } {
  const t = testCount / 50; // normalize 0..1
  const x = CHART.originX + t * CHART.width;
  const y = 180 + 580 * (1 / (1 + 0.08 * testCount));
  return { x, y };
}
