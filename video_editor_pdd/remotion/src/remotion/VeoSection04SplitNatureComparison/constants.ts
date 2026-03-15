// Component-level constants for VeoSection04SplitNatureComparison
// Split-screen comparison with center-outward wipe: 30 frames (~1.0s at 30fps)

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
} as const;

export const COLORS = {
  background: '#000000',
  divider: '#C9A84C',
  dividerGlow: 'rgba(201, 168, 76, 0.4)',
  labelBackground: 'rgba(0, 0, 0, 0.6)',
  labelText: '#FFFFFF',
} as const;

export const TYPOGRAPHY = {
  label: {
    fontSize: 18,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 600 as const,
  },
} as const;

export const DIMENSIONS = {
  leftPanelX: 0,
  leftPanelWidth: 956,
  rightPanelX: 964,
  rightPanelWidth: 956,
  panelHeight: 1080,
  dividerX: 960,
  dividerWidth: 3,
  dividerHeight: 1080,
  dividerGlowRadius: 12,
  labelInsetX: 24,
  labelBottomOffset: 24,
  labelPaddingX: 16,
  labelPaddingY: 8,
  labelRadius: 4,
} as const;

export const ANIMATION = {
  // Frame 0–8: split wipe from center outward
  wipeStart: 0,
  wipeEnd: 8,

  // Frame 8–10: labels fade in
  labelFadeStart: 8,
  labelFadeEnd: 10,

  // Frame 10–30: hold with divider shimmer
  shimmerStart: 10,
  shimmerEnd: 30,
  shimmerOpacityMin: 0.85,
  shimmerOpacityMax: 1.0,
} as const;

export type SplitComparisonLayout = {
  width: number;
  height: number;
  scaleX: number;
  scaleY: number;
  uniformScale: number;
  typography: {
    label: typeof TYPOGRAPHY.label;
  };
};

export const resolveSplitComparisonLayout = (
  width: number,
  height: number,
): SplitComparisonLayout => {
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
      label: {
        ...TYPOGRAPHY.label,
        fontSize: Math.max(14, TYPOGRAPHY.label.fontSize * uniformScale),
      },
    },
  };
};
