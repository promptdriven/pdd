// AnimationSection04AnimatedLineGraph constants

export const COLORS = {
  background: '#0f172a',
  gridLine: '#1e293b',
  axisLabel: '#64748b',
  legendText: '#cbd5e1',
  series1: '#3b82f6',
  series2: '#8b5cf6',
} as const;

export const DIMENSIONS = {
  canvasWidth: 1920,
  canvasHeight: 1080,
  graphWidth: 1400,
  graphHeight: 700,
  graphCenterX: 960,
  graphCenterY: 540,
} as const;

export const GRAPH_AREA = {
  left: DIMENSIONS.graphCenterX - DIMENSIONS.graphWidth / 2,
  right: DIMENSIONS.graphCenterX + DIMENSIONS.graphWidth / 2,
  top: DIMENSIONS.graphCenterY - DIMENSIONS.graphHeight / 2,
  bottom: DIMENSIONS.graphCenterY + DIMENSIONS.graphHeight / 2,
};

export const DATA = {
  xLabels: ['Jan', 'Feb', 'Mar', 'Apr', 'May', 'Jun', 'Jul'],
  series1: [30, 45, 38, 62, 58, 75, 68],
  series2: [20, 35, 48, 45, 65, 58, 72],
  yMin: 0,
  yMax: 100,
} as const;

export const TIMING = {
  gridFadeIn: { start: 0, duration: 15 },
  legendFadeIn: { start: 15, duration: 5 },
  series1Draw: { start: 20, duration: 60 },
  series2Draw: { start: 40, duration: 60 },
  totalDuration: 120,
} as const;

export const TYPOGRAPHY = {
  axisLabel: {
    fontFamily: 'Inter',
    fontWeight: '500',
    fontSize: 14,
  },
  legend: {
    fontFamily: 'Inter',
    fontWeight: '500',
    fontSize: 16,
  },
} as const;
