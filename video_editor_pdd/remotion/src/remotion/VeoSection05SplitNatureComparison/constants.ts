// Component-level constants for VeoSection05SplitNatureComparison
// Single-frame flash card — no animation timing needed.

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#000000',
  divider: 'rgba(255, 255, 255, 0.9)',
  dividerGlow: 'rgba(255, 255, 255, 0.35)',
  labelBackground: 'rgba(11, 17, 32, 0.7)',
  labelText: '#FFFFFF',
  headerText: '#FFFFFF',
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
  leftPanelX: 0,
  leftPanelY: 0,
  panelWidth: 958,
  panelHeight: 1080,
  panelBorderRadius: 0,
  rightPanelX: 962,
  rightPanelY: 0,
  dividerX: 958,
  dividerY: 0,
  dividerWidth: 4,
  dividerHeight: 1080,
  dividerGlowRadius: 8,
  labelInsetX: 40,
  labelBottomOffset: 40,
  labelPaddingX: 16,
  labelPaddingY: 8,
  labelRadius: 20,
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
