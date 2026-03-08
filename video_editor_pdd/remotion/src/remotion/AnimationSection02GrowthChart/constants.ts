export const CHART_CONFIG = {
  // Canvas
  width: 1920,
  height: 1080,
  background: '#0F172A',

  // Chart area
  chartArea: {
    width: 1400,
    height: 700,
    marginTop: 190,
    marginLeft: 260,
    marginRight: 260,
    marginBottom: 190,
  },

  // Colors
  colors: {
    background: '#0F172A',
    gridLine: '#1E293B',
    axisLine: '#475569',
    dataLine: '#3B82F6',
    dataLineGlow: '#3B82F6',
    dataPoint: '#60A5FA',
    dataPointStroke: '#3B82F6',
    title: '#F1F5F9',
    label: '#94A3B8',
    valueCallout: '#3B82F6',
  },

  // Stroke widths
  strokeWidths: {
    gridLine: 1,
    axisLine: 2,
    dataLine: 3,
    dataPoint: 3,
  },

  // Data points
  dataPointRadius: 8,

  // Grid
  grid: {
    rows: 8,
    cols: 6,
    opacity: 0.1,
  },

  // Typography
  typography: {
    title: {
      fontFamily: 'Inter',
      fontWeight: '600',
      fontSize: 48,
      color: '#F1F5F9',
      x: 260,
      y: 120,
    },
    axisLabel: {
      fontFamily: 'Inter',
      fontWeight: '400',
      fontSize: 24,
      color: '#94A3B8',
    },
    valueCallout: {
      fontFamily: 'Inter',
      fontWeight: '700',
      fontSize: 20,
      color: '#3B82F6',
    },
  },
};

export const GROWTH_DATA = [
  { x: 0, y: 25000, label: 'Q1' },
  { x: 1, y: 32000, label: 'Q2' },
  { x: 2, y: 65000, label: 'Q3' },
  { x: 3, y: 98000, label: 'Q4 Est' },
  { x: 4, y: 125000, label: 'Q1 2025' },
  { x: 5, y: 156000, label: 'Q2 2025' },
  { x: 6, y: 178000, label: 'Q3 2025' },
  { x: 7, y: 195000, label: 'Q4 2025' },
];

export const AXIS_CONFIG = {
  xAxisY: 880,
  yAxisX: 260,
  xLabels: ['Q1', 'Q2', 'Q3', 'Q4'],
  yLabels: ['0K', '50K', '100K', '150K', '200K'],
};

export const ANIMATION_TIMING = {
  gridFadeIn: { start: 0, duration: 20 },
  axisDrawIn: { start: 20, duration: 15 },
  labelsFadeIn: { start: 35, duration: 15 },
  lineDrawIn: { start: 50, duration: 60 },
  pointsAppear: { start: 60, duration: 60 },
  finalPulse: { start: 120, duration: 30 },
  totalDuration: 150,
};
