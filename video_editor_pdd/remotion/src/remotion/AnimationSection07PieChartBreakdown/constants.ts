// Component-level constants for AnimationSection07PieChartBreakdown

export const CANVAS = {
  WIDTH: 1920,
  HEIGHT: 1080,
  BACKGROUND: '#0F172A',
} as const;

export const CHART = {
  CENTER_X: 700,
  CENTER_Y: 540,
  RADIUS: 280,
  EXPLODE_OFFSET: 20,
} as const;

export const PIE_DATA = [
  {
    id: 'enterprise',
    label: 'Enterprise',
    percentage: 45,
    color: '#3B82F6',
    startAngle: 0,
    endAngle: 162,
    explode: true,
  },
  {
    id: 'smb',
    label: 'SMB',
    percentage: 30,
    color: '#8B5CF6',
    startAngle: 162,
    endAngle: 270,
    explode: false,
  },
  {
    id: 'startup',
    label: 'Startup',
    percentage: 18,
    color: '#10B981',
    startAngle: 270,
    endAngle: 335,
    explode: false,
  },
  {
    id: 'other',
    label: 'Other',
    percentage: 7,
    color: '#F59E0B',
    startAngle: 335,
    endAngle: 360,
    explode: false,
  },
] as const;

export const TITLE = {
  TEXT: 'Market Share Distribution 2024',
  FONT_SIZE: 52,
  COLOR: '#F1F5F9',
  POSITION_X: 960,
  POSITION_Y: 120,
} as const;

export const LABEL = {
  FONT_SIZE: 32,
  COLOR: '#FFFFFF',
  LINE_LENGTH: 60,
  LINE_WIDTH: 2,
  BACKGROUND_OPACITY: 0.8,
  PADDING: 12,
} as const;

export const LEGEND = {
  POSITION_X: 1200,
  POSITION_Y: 400,
  ITEM_HEIGHT: 60,
  CIRCLE_SIZE: 24,
  LABEL_FONT_SIZE: 28,
  LABEL_COLOR: '#E2E8F0',
} as const;

export const TIMING = {
  TOTAL_FRAMES: 150,
  FPS: 30,
  TITLE_START: 0,
  TITLE_DURATION: 20,
  SLICE_1_START: 20,
  SLICE_2_START: 40,
  SLICE_3_START: 60,
  SLICE_4_START: 80,
  SLICE_DURATION: 20,
  LABELS_START: 100,
  LABELS_DURATION: 20,
  LEGEND_START: 120,
  LEGEND_DURATION: 20,
  ROTATION_START: 140,
  ROTATION_DURATION: 10,
} as const;
