// Component-level constants for VeoSection07SplitComparison

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0F1419',
  divider: '#475569',
  dividerGlow: '#3B82F680',
  oceanLabel: '#D4A574',
  forestLabel: '#86EFAC',
  oceanTint: '#F59E0B08',
  forestTint: '#22C55E08',
  badgeBg: '#1E293BCC',
  badgeBorder: '#D4A57460',
  badgeText: '#F8FAFC',
  metricText: '#94A3B8',
  metricValue: '#F1F5F9',
  metricBarBg: '#1E293B',
  metricBarOcean: '#F59E0B',
  metricBarForest: '#22C55E',
  headerText: '#E2E8F0',
};

export const POSITIONS = {
  dividerX: 960,
  leftPanelCenter: 478,
  rightPanelCenter: 1442,
  labelY: 120,
  badgeY: 540,
  metricsStartY: 780,
};

export const DIMENSIONS = {
  dividerWidth: 3,
  badgeWidth: 160,
  badgeHeight: 48,
  badgeBorderRadius: 24,
  leftPanelWidth: 955,
  rightPanelStart: 965,
  videoHeight: 620,
  metricBarHeight: 6,
  metricBarWidth: 280,
};

export const TYPOGRAPHY = {
  label: {
    fontFamily: 'Inter, sans-serif',
    fontWeight: 600 as const,
    fontSize: 24,
  },
  badge: {
    fontFamily: 'Inter, sans-serif',
    fontWeight: 700 as const,
    fontSize: 17,
  },
  metric: {
    fontFamily: 'Inter, sans-serif',
    fontWeight: 500 as const,
    fontSize: 15,
  },
  metricValue: {
    fontFamily: 'Inter, sans-serif',
    fontWeight: 700 as const,
    fontSize: 18,
  },
  header: {
    fontFamily: 'Inter, sans-serif',
    fontWeight: 700 as const,
    fontSize: 28,
  },
};

export const ANIMATION = {
  dividerWipeStart: 0,
  dividerWipeEnd: 18,
  leftPanelFadeStart: 0,
  leftPanelFadeEnd: 20,
  rightPanelFadeStart: 8,
  rightPanelFadeEnd: 28,
  headerFadeStart: 0,
  headerFadeEnd: 15,
  badgePopStart: 30,
  badgePopEnd: 45,
  metricsStaggerDelay: 8,
  metricsStart: 40,
  metricsDuration: 20,
  totalDuration: 90,
  labelTranslateDistance: 15,
  kenBurnsScaleStart: 1.0,
  kenBurnsScaleEnd: 1.06,
};

export const METRICS = [
  { label: 'Resolution', oceanValue: '4K', forestValue: '4K', oceanPercent: 100, forestPercent: 100 },
  { label: 'Motion Quality', oceanValue: '9.2', forestValue: '9.4', oceanPercent: 92, forestPercent: 94 },
  { label: 'Color Fidelity', oceanValue: '9.5', forestValue: '9.1', oceanPercent: 95, forestPercent: 91 },
];
