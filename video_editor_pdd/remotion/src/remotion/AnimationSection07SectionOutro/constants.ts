// Component-level constants for AnimationSection07SectionOutro
// Duration: ~0.7s (21 frames @ 30fps)

export const CANVAS = {
  width: 1920,
  height: 1080,
} as const;

export const COLORS = {
  background: '#1E293B',
  fadeToBlack: '#000000',
  checkmark: '#22C55E',
  text: '#CBD5E1',
} as const;

export const TYPOGRAPHY = {
  text: {
    fontFamily: "'Inter', sans-serif",
    fontSize: 28,
    fontWeight: 500 as const,
  },
} as const;

export const DIMENSIONS = {
  checkmarkSize: 48,
  checkmarkStrokeWidth: 3,
  checkmarkCenterX: 960,
  checkmarkCenterY: 480,
  textCenterY: 560,
} as const;

export const ANIMATION_TIMING = {
  // Frame 0-9: Checkmark SVG stroke draws in
  checkmarkDrawStart: 0,
  checkmarkDrawEnd: 9,
  // Frame 6-12: "Section Complete" text fades in
  textFadeStart: 6,
  textFadeEnd: 12,
  // Frame 12-15: Hold at full visibility
  // Frame 15-21: All elements fade out; background fades to black
  fadeOutStart: 15,
  fadeOutEnd: 21,
  totalDuration: 21,
} as const;

// Checkmark SVG path and approximate total stroke length
export const CHECKMARK_PATH = 'M8 24 L20 36 L40 12';
// Left leg (8,24)->(20,36): sqrt(12^2+12^2) ≈ 17, Right leg (20,36)->(40,12): sqrt(20^2+24^2) ≈ 31, total ≈ 48
export const CHECKMARK_PATH_LENGTH = 48;
