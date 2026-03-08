// Component-level constants for AnimationSection06FrameworkComparison

export const CANVAS = {
  width: 1920,
  height: 1080,
  halfWidth: 960,
};

export const COLORS = {
  leftBackground: '#1E3A8A',
  rightBackground: '#334155',
  divider: '#94A3B8',
  labelText: '#FFFFFF',
  leftSubLabel: '#93C5FD',
  rightSubLabel: '#CBD5E1',
  barColors: ['#38BDF8', '#22C55E', '#38BDF8', '#22C55E'] as const,
  glowBorder: '#3B82F6',
  filmReelIcon: '#64748B',
};

export const TYPOGRAPHY = {
  label: {
    fontSize: 48,
    fontFamily: 'Inter',
    fontWeight: 'bold' as const,
  },
  subLabel: {
    fontSize: 24,
    fontFamily: 'Inter',
    fontWeight: 'normal' as const,
  },
};

export const POSITIONS = {
  leftLabelX: 240,
  leftLabelY: 200,
  leftSubLabelY: 260,
  rightLabelX: 1200,
  rightLabelY: 200,
  rightSubLabelY: 260,
  labelSlideStartY: 180,
  labelSlideEndY: 200,
};

export const DIMENSIONS = {
  dividerWidth: 2,
  barWidth: 60,
  barGap: 16,
  glowBorderWidth: 2,
  filmReelSize: 120,
};

export const BAR_DATA = {
  heights: [0.35, 0.55, 0.8, 0.6],
  maxBarHeight: 180,
};

export const ANIMATION_TIMING = {
  // Left panel fade-in: frame 0-20
  leftFadeStart: 0,
  leftFadeEnd: 20,
  // Mini bar chart: frame 5-25, staggered 5 frames each
  barGrowStart: 5,
  barStagger: 5,
  barGrowDuration: 15,
  // Divider draw: frame 15-35
  dividerStart: 15,
  dividerEnd: 35,
  // Right panel fade-in: frame 25-45
  rightFadeStart: 25,
  rightFadeEnd: 45,
  // Glow pulse: frame 40-60
  glowPulseStart: 40,
  glowPulseMid: 50,
  glowPulseEnd: 60,
  // Total
  totalDuration: 60,
};

export const RIGHT_PANEL_OPACITY = 0.6;
