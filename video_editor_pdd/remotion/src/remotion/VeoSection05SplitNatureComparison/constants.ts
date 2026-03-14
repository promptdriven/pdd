// Component-level constants for VeoSection05SplitNatureComparison
// Split-screen comparison: 30 frames (~1.0s at 30fps)

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
} as const;

export const COLORS = {
  background: '#000000',
  divider: 'rgba(255, 255, 255, 0.9)',
  dividerGlow: 'rgba(255, 255, 255, 0.35)',
  labelBackground: 'rgba(11, 17, 32, 0.7)',
  labelText: '#FFFFFF',
} as const;

export const TYPOGRAPHY = {
  label: {
    fontSize: 20,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 600 as const,
  },
} as const;

export const DIMENSIONS = {
  leftPanelX: 0,
  leftPanelY: 0,
  panelWidth: 958,
  panelHeight: 1080,
  rightPanelX: 962,
  rightPanelY: 0,
  dividerX: 958,
  dividerWidth: 4,
  dividerHeight: 1080,
  dividerGlowRadius: 8,
  labelInsetX: 40,
  labelBottomOffset: 60,
  labelPaddingX: 16,
  labelPaddingY: 8,
  labelRadius: 20,
} as const;

export const ANIMATION = {
  // Frame 0–8: panels scale from 1.1→1.0 (zoom-out settle)
  panelZoomStart: 0,
  panelZoomEnd: 8,
  panelScaleFrom: 1.1,
  panelScaleTo: 1.0,

  // Frame 8–18: divider draws top-to-bottom (height 0→1080)
  dividerDrawStart: 8,
  dividerDrawEnd: 18,

  // Frame 14–22: left label fades in (opacity 0→1, translateY +10→0)
  leftLabelStart: 14,
  leftLabelEnd: 22,

  // Frame 18–26: right label fades in (opacity 0→1, translateY +10→0)
  rightLabelStart: 18,
  rightLabelEnd: 26,

  // Frame 26–30: hold
  labelTranslateY: 10,
} as const;

export type SplitNatureComparisonLayout = {
  width: number;
  height: number;
  scaleX: number;
  scaleY: number;
  uniformScale: number;
  typography: {
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
      label: {
        ...TYPOGRAPHY.label,
        fontSize: Math.max(14, TYPOGRAPHY.label.fontSize * uniformScale),
      },
    },
  };
};
