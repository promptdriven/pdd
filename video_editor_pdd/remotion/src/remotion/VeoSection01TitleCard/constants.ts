// Component-level constants for VeoSection01TitleCard

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  gradientTop: '#0B1D3A',
  gradientBottom: '#162D50',
  titleText: '#FFFFFF',
  rule: '#5B9BD5',
  particle: '#FFFFFF',
};

export const TYPOGRAPHY = {
  title: {
    fontSize: 64,
    fontFamily: 'Inter',
    fontWeight: 'bold' as const,
  },
};

export const ANIMATION = {
  // Background gradient fades in from black
  backgroundFadeStart: 0,
  backgroundFadeEnd: 15,
  // Title text fades in and shifts up 10px
  titleFadeStart: 15,
  titleFadeEnd: 45,
  // Horizontal rule draws outward from center
  ruleFadeStart: 30,
  ruleFadeEnd: 60,
  // Particle drift runs full duration
  particleDurationFrames: 90,
  totalDuration: 90,
};

export const DIMENSIONS = {
  ruleWidth: 200,
  ruleHeight: 2,
  particleCount: 18,
  particleMinRadius: 2,
  particleMaxRadius: 4,
  particleOpacity: 0.15,
  titleRuleGap: 24,
};

export type TitleCardLayout = {
  width: number;
  height: number;
  typography: {
    title: typeof TYPOGRAPHY.title;
  };
  dimensions: typeof DIMENSIONS;
};

export const resolveTitleCardLayout = (
  width: number,
  height: number
): TitleCardLayout => {
  const scaleX = width / BASE_CANVAS.width;
  const scaleY = height / BASE_CANVAS.height;
  const uniformScale = Math.min(scaleX, scaleY);

  return {
    width,
    height,
    typography: {
      title: {
        ...TYPOGRAPHY.title,
        fontSize: Math.max(34, TYPOGRAPHY.title.fontSize * uniformScale),
      },
    },
    dimensions: {
      ruleWidth: DIMENSIONS.ruleWidth * scaleX,
      ruleHeight: Math.max(1.5, DIMENSIONS.ruleHeight * scaleY),
      particleCount: DIMENSIONS.particleCount,
      particleMinRadius: Math.max(1.5, DIMENSIONS.particleMinRadius * uniformScale),
      particleMaxRadius: Math.max(3, DIMENSIONS.particleMaxRadius * uniformScale),
      particleOpacity: DIMENSIONS.particleOpacity,
      titleRuleGap: DIMENSIONS.titleRuleGap * scaleY,
    },
  };
};
