// Component-level constants for VeoSection03FeatureComparisonChart

export const CANVAS = {
  WIDTH: 1920,
  HEIGHT: 1080,
  BACKGROUND: '#0F1419', // dark slate
};

export const GRID = {
  COLOR: '#2A2E35',
  OPACITY: 0.3,
  POSITIONS: [0.25, 0.5, 0.75, 1.0], // 25%, 50%, 75%, 100%
};

export const PLATFORMS = {
  VEO_2: {
    name: 'VEO 2',
    yPosition: 250,
    metrics: {
      Quality: 9.5,
      Speed: 9.0,
      Cost: 8.5,
      Control: 9.0,
    },
  },
  TRADITIONAL: {
    name: 'Traditional Tools',
    yPosition: 450,
    metrics: {
      Quality: 8.0,
      Speed: 5.0,
      Cost: 4.0,
      Control: 9.5,
    },
  },
  AI_PLATFORM_B: {
    name: 'AI Platform B',
    yPosition: 650,
    metrics: {
      Quality: 7.5,
      Speed: 8.0,
      Cost: 7.0,
      Control: 6.5,
    },
  },
};

export const METRIC_COLORS = {
  Quality: '#00D9FF', // electric blue
  Speed: '#7C3AED', // purple
  Cost: '#10B981', // green
  Control: '#F59E0B', // amber
};

export const CHART_DIMENSIONS = {
  BAR_HEIGHT: 40,
  BAR_CORNER_RADIUS: 8,
  METRIC_SPACING: 60,
  CHART_START_X: 400,
  CHART_WIDTH: 1200,
  LABEL_X: 100,
};

export const TYPOGRAPHY = {
  TITLE: {
    FONT_FAMILY: 'Inter',
    FONT_WEIGHT: 'bold',
    FONT_SIZE: 48,
    COLOR: '#FFFFFF',
  },
  PLATFORM_LABEL: {
    FONT_FAMILY: 'Inter',
    FONT_WEIGHT: '600',
    FONT_SIZE: 28,
    COLOR: '#E0E6ED',
  },
  METRIC_LABEL: {
    FONT_FAMILY: 'Inter',
    FONT_WEIGHT: '500',
    FONT_SIZE: 22,
    COLOR: '#9CA3AF',
  },
  VALUE_LABEL: {
    FONT_FAMILY: 'Inter',
    FONT_WEIGHT: '500',
    FONT_SIZE: 20,
    COLOR: '#FFFFFF',
  },
};

export const ANIMATION_TIMING = {
  LABEL_FADE_DURATION: 15, // frames
  BAR_GROWTH_DURATION: 30, // frames
  METRIC_STAGGER: 10, // frames between each metric bar
  VEO_START: 15,
  TRADITIONAL_START: 45,
  AI_PLATFORM_START: 75,
  HOLD_START: 105,
};
