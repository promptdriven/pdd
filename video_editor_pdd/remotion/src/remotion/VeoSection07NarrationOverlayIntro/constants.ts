// Component-level constants for VeoSection07NarrationOverlayIntro
// Duration: ~4s (120 frames @ 30fps)

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  pillFill: 'rgba(11,29,58,0.7)',
  pillBorder: 'rgba(91,155,213,0.3)',
  accentGradientStart: '#5B9BD5',
  accentGradientEnd: '#D4A843',
  narrationText: '#FFFFFF',
  progressBar: '#5B9BD5',
};

export const TYPOGRAPHY = {
  narration: {
    fontSize: 22,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 500 as const,
    lineHeight: 1.5,
  },
};

export const PILL = {
  x: 80,
  y: 900,
  width: 800,
  height: 100,
  borderRadius: 16,
  backdropBlur: 12,
  textMaxWidth: 720,
  textPaddingX: 24,
  textPaddingY: 20,
};

export const NARRATION_TEXT =
  'This is the second section of the integration test video.';

export const ANIMATION = {
  // Frame 0-20: Pill slides in from left
  pillSlideStart: 0,
  pillSlideEnd: 20,
  pillSlideOffset: -100,

  // Frame 10-15: Accent gradient bar fades in
  accentFadeStart: 10,
  accentFadeEnd: 15,

  // Frame 20-90: Narration text types on
  typeOnStart: 20,
  typeOnEnd: 90,

  // Frame 0-120: Progress bar fills
  progressStart: 0,
  progressEnd: 120,

  // Frame 100-120: Entire overlay fades out
  fadeOutStart: 100,
  fadeOutEnd: 120,

  totalDuration: 120,
};

export const DIMENSIONS = {
  accentBarHeight: 3,
  progressBarHeight: 2,
  progressBarOpacity: 0.4,
};

export type NarrationOverlayLayout = {
  width: number;
  height: number;
  scaleX: number;
  scaleY: number;
  uniformScale: number;
  typography: {
    narration: {
      fontSize: number;
      fontFamily: string;
      fontWeight: number;
      lineHeight: number;
    };
  };
  pill: {
    x: number;
    y: number;
    width: number;
    height: number;
    borderRadius: number;
    backdropBlur: number;
    textMaxWidth: number;
    textPaddingX: number;
    textPaddingY: number;
  };
  dimensions: {
    accentBarHeight: number;
    progressBarHeight: number;
    progressBarOpacity: number;
    progressBarGap: number;
  };
};

export const resolveNarrationOverlayLayout = (
  width: number,
  height: number,
): NarrationOverlayLayout => {
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
      narration: {
        ...TYPOGRAPHY.narration,
        fontSize: Math.max(16, TYPOGRAPHY.narration.fontSize * uniformScale),
      },
    },
    pill: {
      x: PILL.x * scaleX,
      y: PILL.y * scaleY,
      width: PILL.width * scaleX,
      height: PILL.height * scaleY,
      borderRadius: Math.max(12, PILL.borderRadius * uniformScale),
      backdropBlur: Math.max(8, PILL.backdropBlur * uniformScale),
      textMaxWidth: PILL.textMaxWidth * scaleX,
      textPaddingX: PILL.textPaddingX * scaleX,
      textPaddingY: PILL.textPaddingY * scaleY,
    },
    dimensions: {
      accentBarHeight: Math.max(2, DIMENSIONS.accentBarHeight * scaleY),
      progressBarHeight: Math.max(1.5, DIMENSIONS.progressBarHeight * scaleY),
      progressBarOpacity: DIMENSIONS.progressBarOpacity,
      progressBarGap: 8 * scaleY,
    },
  };
};
