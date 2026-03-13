// Component-level constants for VeoSection01TitleCard
// Duration: ~3s (90 frames @ 30fps)

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
    fontFamily: "'Inter', sans-serif",
    fontWeight: 700 as const,
  },
};

export const ANIMATION = {
  // Frame 0-15: Background gradient fades in from black (linear)
  backgroundFadeStart: 0,
  backgroundFadeEnd: 15,
  // Frame 15-45: Title text fades in with parallax shift (easeOutCubic)
  titleFadeStart: 15,
  titleFadeEnd: 45,
  titleShiftPx: 10,
  // Frame 30-60: Horizontal rule scales outward from centre (easeInOutQuad)
  ruleFadeStart: 30,
  ruleFadeEnd: 60,
  // Frame 0-90: Particle drift runs continuously
  totalDuration: 90,
};

export const DIMENSIONS = {
  ruleWidth: 200,
  ruleHeight: 2,
  particleCount: 18,
  particleMinRadius: 2,
  particleMaxRadius: 4,
  particleOpacity: 0.15,
  particleMinSpeed: 1.5,
  particleMaxSpeed: 4.0,
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
  height: number,
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
      particleMinSpeed: DIMENSIONS.particleMinSpeed * uniformScale,
      particleMaxSpeed: DIMENSIONS.particleMaxSpeed * uniformScale,
      titleRuleGap: DIMENSIONS.titleRuleGap * scaleY,
    },
  };
};
