// Component-level constants for VeoSection08SectionEndCard
// Duration: ~3s (90 frames @ 30fps)

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  gradientTop: '#0B1D3A',
  gradientBottom: '#162D50',
  ring: '#5B9BD5',
  checkmark: '#40916C',
  labelText: '#FFFFFF',
  rule: '#5B9BD5',
  bokeh: '#FFFFFF',
} as const;

export const TYPOGRAPHY = {
  label: {
    fontSize: 36,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 600 as const,
  },
} as const;

export const DIMENSIONS = {
  ringRadius: 80,
  ringStroke: 4,
  ringCenterX: 960,
  ringCenterY: 460,
  checkmarkSize: 32,
  checkmarkStrokeWidth: 3,
  labelY: 600,
  ruleWidth: 160,
  ruleHeight: 2,
  ruleGapBelow: 16,
  bokehCount: 12,
  bokehMinRadius: 3,
  bokehMaxRadius: 8,
  bokehMinOpacity: 0.08,
  bokehMaxOpacity: 0.15,
  bokehBlur: 3,
  bokehMinSpeed: 0.5,
  bokehMaxSpeed: 2.0,
} as const;

export const ANIMATION = {
  // Frame 0-10: Background gradient fades in (opacity 0 → 1)
  backgroundFadeStart: 0,
  backgroundFadeEnd: 10,
  // Frame 0-90: Bokeh particles drift continuously
  // Frame 10-40: Completion ring draws clockwise (0° → 360°)
  ringDrawStart: 10,
  ringDrawEnd: 40,
  // Frame 40-55: Checkmark scales in with bounce
  checkmarkStart: 40,
  checkmarkEnd: 55,
  // Frame 50-70: Label fades in with translateY
  labelFadeStart: 50,
  labelFadeEnd: 70,
  labelShiftPx: 10,
  // Frame 60-80: Horizontal rule scales outward
  ruleScaleStart: 60,
  ruleScaleEnd: 80,
  totalDuration: 90,
} as const;

export const LABEL_TEXT = 'Veo Section Complete';

export type EndCardLayout = {
  width: number;
  height: number;
  scaleX: number;
  scaleY: number;
  uniformScale: number;
  typography: {
    label: {
      fontSize: number;
      fontFamily: string;
      fontWeight: number;
    };
  };
  dimensions: {
    ringRadius: number;
    ringStroke: number;
    ringCenterX: number;
    ringCenterY: number;
    checkmarkSize: number;
    checkmarkStrokeWidth: number;
    labelY: number;
    ruleWidth: number;
    ruleHeight: number;
    ruleGapBelow: number;
  };
};

export const resolveEndCardLayout = (
  width: number,
  height: number,
): EndCardLayout => {
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
        fontSize: Math.max(24, TYPOGRAPHY.label.fontSize * uniformScale),
      },
    },
    dimensions: {
      ringRadius: DIMENSIONS.ringRadius * uniformScale,
      ringStroke: Math.max(2, DIMENSIONS.ringStroke * uniformScale),
      ringCenterX: DIMENSIONS.ringCenterX * scaleX,
      ringCenterY: DIMENSIONS.ringCenterY * scaleY,
      checkmarkSize: DIMENSIONS.checkmarkSize * uniformScale,
      checkmarkStrokeWidth: Math.max(2, DIMENSIONS.checkmarkStrokeWidth * uniformScale),
      labelY: DIMENSIONS.labelY * scaleY,
      ruleWidth: DIMENSIONS.ruleWidth * scaleX,
      ruleHeight: Math.max(1.5, DIMENSIONS.ruleHeight * scaleY),
      ruleGapBelow: DIMENSIONS.ruleGapBelow * scaleY,
    },
  };
};
