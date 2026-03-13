// Component-level constants for VeoSection05SplitNatureComparison
// Single-frame flash card — no animation timing needed.

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0D1B2A',
  divider: '#4DA8DA',
  dividerGlow: '#4DA8DA',
  leftLabel: '#FFD4A8',
  rightLabel: '#A8E6CF',
  headerText: '#FFFFFF',
  vignette: 'rgba(0, 0, 0, 0.5)',
};

export const TYPOGRAPHY = {
  header: {
    fontSize: 32,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 700 as const,
    letterSpacing: 8,
  },
  label: {
    fontSize: 20,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 600 as const,
  },
};

export const DIMENSIONS = {
  // Left panel: 940×810 at (10, 140)
  leftPanelX: 10,
  leftPanelY: 140,
  panelWidth: 940,
  panelHeight: 810,
  panelBorderRadius: 8,
  // Right panel: 940×810 at (970, 140)
  rightPanelX: 970,
  rightPanelY: 140,
  // Center divider at x=960, 2px wide, height 810px
  dividerX: 960,
  dividerY: 140,
  dividerWidth: 2,
  dividerHeight: 810,
  dividerGlowRadius: 12,
  // Labels below panels at y=980
  labelY: 980,
  leftLabelCenterX: 480,   // centered under left panel
  rightLabelCenterX: 1440, // centered under right panel
  // Header at y=60
  headerY: 60,
};

export type SplitNatureComparisonLayout = {
  width: number;
  height: number;
  scaleX: number;
  scaleY: number;
  uniformScale: number;
  typography: {
    header: typeof TYPOGRAPHY.header;
    label: typeof TYPOGRAPHY.label;
  };
};

export const resolveSplitNatureComparisonLayout = (
  width: number,
  height: number,
): SplitNatureComparisonLayout => {
  const scaleX = width / BASE_CANVAS.width;
  const scaleY = height / BASE_CANVAS.height;
  const uniformScale = Math.min(scaleX, scaleY);

  return {
    width,
    height,
    scaleX,
    scaleY,
    uniformScale,
    typography: {
      header: {
        ...TYPOGRAPHY.header,
        fontSize: Math.max(20, TYPOGRAPHY.header.fontSize * uniformScale),
        letterSpacing: Math.max(4, TYPOGRAPHY.header.letterSpacing * uniformScale),
      },
      label: {
        ...TYPOGRAPHY.label,
        fontSize: Math.max(14, TYPOGRAPHY.label.fontSize * uniformScale),
      },
    },
  };
};
