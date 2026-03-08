// Component-level constants for AnimationSection06SplitBeforeAfter

export const CANVAS = {
  width: 1920,
  height: 1080,
  dividerX: 960,
};

export const COLORS = {
  background: '#0F172A',
  leftPanel: '#1E293B',
  rightGradientStart: '#1E3A8A',
  rightGradientEnd: '#0F172A',
  divider: '#3B82F6',
  beforeLabel: '#94A3B8',
  afterLabel: '#60A5FA',
  staticBar: '#334155',
  filmIcon: '#64748B',
  codeIcon: '#3B82F6',
  codeToken: '#3B82F6',
};

export const TYPOGRAPHY = {
  label: {
    fontSize: 48,
    fontFamily: 'Inter',
    fontWeight: 'bold' as const,
  },
  codeToken: {
    fontSize: 16,
    fontFamily: 'JetBrains Mono, monospace',
    fontWeight: 'normal' as const,
  },
};

export const POSITIONS = {
  labelY: 120,
  iconY: 200,
  leftLabelX: 240,
  rightLabelX: 1200,
  barStartY: 350,
  barSpacing: 100,
};

export const DIMENSIONS = {
  dividerWidth: 4,
  dividerGlowBlur: 20,
  iconSize: 40,
  barHeight: 24,
  barWidths: [300, 220, 260],
  tokenPillHeight: 32,
  tokenPillPadding: 16,
};

export const ANIMATION_TIMING = {
  // Left panel slide in
  leftSlideStart: 0,
  leftSlideEnd: 15,
  // Divider wipe
  dividerStart: 8,
  dividerEnd: 20,
  // Right panel slide in
  rightSlideStart: 12,
  rightSlideEnd: 25,
  // Before label + bars
  beforeLabelStart: 20,
  beforeLabelEnd: 30,
  barsStart: 22,
  barStagger: 4,
  // After label + tokens
  afterLabelStart: 25,
  afterLabelEnd: 35,
  tokensStart: 30,
  // Hold
  totalDuration: 60,
};

export const CODE_TOKENS = [
  '<Sequence>',
  'spring()',
  'interpolate()',
  'useCurrentFrame()',
  '<AbsoluteFill>',
];
