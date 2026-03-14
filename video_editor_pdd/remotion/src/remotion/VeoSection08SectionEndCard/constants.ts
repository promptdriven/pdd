// Component-level constants for VeoSection08SectionEndCard
// Duration: ~0.8s (24 frames @ 30fps)

export const COLORS = {
  background: '#0B1120',
  checkmark: '#10B981',
  titleText: '#FFFFFF',
  rule: '#C9A84C',
  subtitleText: '#A0AEC0',
} as const;

export const TYPOGRAPHY = {
  title: {
    fontSize: 42,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 700 as const,
  },
  subtitle: {
    fontSize: 20,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 400 as const,
  },
} as const;

export const DIMENSIONS = {
  // Checkmark circle
  checkmarkCenterX: 960,
  checkmarkCenterY: 380,
  checkmarkSize: 80,
  checkmarkStrokeWidth: 3,
  // Text positions (absolute Y)
  titleY: 500,
  ruleY: 550,
  ruleMaxWidth: 300,
  ruleHeight: 2,
  subtitleY: 590,
} as const;

// Checkmark path in a 0-80 viewBox coordinate system
export const CHECKMARK_PATH = 'M 22 40 L 35 53 L 58 28';
// Segment 1: (22,40)->(35,53) = sqrt(13^2+13^2) ~ 18.4
// Segment 2: (35,53)->(58,28) = sqrt(23^2+25^2) ~ 34.0
// Total ~ 52.4
export const CHECKMARK_PATH_LENGTH = 53;

// Circle circumference for 80px diameter (r=40): 2*pi*40 ~ 251.3
export const CIRCLE_CIRCUMFERENCE = 2 * Math.PI * (DIMENSIONS.checkmarkSize / 2);

export const TITLE_TEXT = 'Veo Section Complete';
export const SUBTITLE_TEXT = '2 Veo clips \u00B7 3 Remotion overlays';

export const ANIMATION = {
  // Frame 0-8: Checkmark icon scales in (easeOutBack) + check path draws
  checkmarkScaleStart: 0,
  checkmarkScaleEnd: 8,
  // Frame 8-14: Title text fades in (opacity 0->1, translateY +15->0)
  titleFadeStart: 8,
  titleFadeEnd: 14,
  titleShiftPx: 15,
  // Frame 14-18: Horizontal rule expands from center
  ruleExpandStart: 14,
  ruleExpandEnd: 18,
  // Frame 18-22: Subtitle fades in (opacity 0->1)
  subtitleFadeStart: 18,
  subtitleFadeEnd: 22,
  // Frame 22-24: Hold, then all elements fade out in final 2 frames
  fadeOutStart: 22,
  fadeOutEnd: 24,
  totalDuration: 24,
} as const;
