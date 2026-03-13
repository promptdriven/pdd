// Component-level constants for VeoSection01TitleCard
// Duration: ~1.3s (38 frames @ 30fps)

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  gradientTop: '#0A1628',
  gradientBottom: '#1B3A5C',
  titleText: '#FFFFFF',
  rule: '#4DA8DA',
  subtitleText: '#8EC8E8',
  particle: '#FFFFFF',
};

export const TYPOGRAPHY = {
  title: {
    fontSize: 72,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 700 as const,
    letterSpacing: 12,
  },
  subtitle: {
    fontSize: 24,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 400 as const,
    letterSpacing: 4,
  },
};

export const ANIMATION = {
  // Frame 0-10: Background fades in + title fades in with slide-up
  backgroundFadeStart: 0,
  backgroundFadeEnd: 10,
  titleFadeStart: 0,
  titleFadeEnd: 10,
  titleShiftPx: 20,
  // Frame 10-22: Rule expands + subtitle fades in
  ruleFadeStart: 10,
  ruleFadeEnd: 22,
  subtitleFadeStart: 10,
  subtitleFadeEnd: 22,
  // Frame 22-38: Hold with ambient glow pulse on rule
  glowPulseStart: 22,
  glowPulseEnd: 38,
  // Total duration
  totalDuration: 38,
};

export const DIMENSIONS = {
  ruleWidth: 600,
  ruleHeight: 2,
  titleY: 440,
  ruleY: 500,
  subtitleY: 540,
  subtitleOpacity: 0.85,
  particleCount: 18,
  particleMinRadius: 2,
  particleMaxRadius: 4,
  particleOpacity: 0.15,
  particleMinSpeed: 1.5,
  particleMaxSpeed: 4.0,
};

export type TitleCardLayout = {
  width: number;
  height: number;
  typography: {
    title: typeof TYPOGRAPHY.title;
    subtitle: typeof TYPOGRAPHY.subtitle;
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
        letterSpacing: TYPOGRAPHY.title.letterSpacing * uniformScale,
      },
      subtitle: {
        ...TYPOGRAPHY.subtitle,
        fontSize: Math.max(16, TYPOGRAPHY.subtitle.fontSize * uniformScale),
        letterSpacing: TYPOGRAPHY.subtitle.letterSpacing * uniformScale,
      },
    },
    dimensions: {
      ruleWidth: DIMENSIONS.ruleWidth * scaleX,
      ruleHeight: Math.max(1.5, DIMENSIONS.ruleHeight * scaleY),
      titleY: DIMENSIONS.titleY * scaleY,
      ruleY: DIMENSIONS.ruleY * scaleY,
      subtitleY: DIMENSIONS.subtitleY * scaleY,
      subtitleOpacity: DIMENSIONS.subtitleOpacity,
      particleCount: DIMENSIONS.particleCount,
      particleMinRadius: Math.max(1.5, DIMENSIONS.particleMinRadius * uniformScale),
      particleMaxRadius: Math.max(3, DIMENSIONS.particleMaxRadius * uniformScale),
      particleOpacity: DIMENSIONS.particleOpacity,
      particleMinSpeed: DIMENSIONS.particleMinSpeed * uniformScale,
      particleMaxSpeed: DIMENSIONS.particleMaxSpeed * uniformScale,
    },
  };
};
