// Component-level constants for VeoSection08SectionEndCard
// Duration: ~1.2s (37 frames @ 30fps)

export const BASE_CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  gradientTop: '#0A1628',
  gradientBottom: '#1B3A5C',
  checkmark: '#6FCF97',
  accent: '#4DA8DA',
  completionText: '#FFFFFF',
  taglineText: 'rgba(255,255,255,0.7)',
  fadeToBlack: '#000000',
} as const;

export const TYPOGRAPHY = {
  completion: {
    fontSize: 48,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 700 as const,
    letterSpacing: 6,
  },
  tagline: {
    fontSize: 20,
    fontFamily: "'Inter', sans-serif",
    fontWeight: 400 as const,
    letterSpacing: 2,
  },
} as const;

export const DIMENSIONS = {
  // Checkmark circle
  circleCenterX: 960,
  circleCenterY: 380,
  circleRadius: 60,
  circleStrokeWidth: 4,
  // Text positions
  completionTextY: 540,
  ruleY: 510,
  ruleWidth: 400,
  ruleHeight: 2,
  taglineY: 600,
  // Checkmark path inside circle
  checkStrokeWidth: 4,
} as const;

// Approximate total length of the check path "M 36 52 L 50 66 L 76 38"
// Segment 1: (36,52)→(50,66) = sqrt(14²+14²) ≈ 19.8
// Segment 2: (50,66)→(76,38) = sqrt(26²+28²) ≈ 38.2
// Total ≈ 58
export const CHECK_PATH = 'M 36 52 L 50 66 L 76 38';
export const CHECK_PATH_LENGTH = 58;

export const COMPLETION_TEXT = 'VEO SECTION COMPLETE';
export const TAGLINE_TEXT = 'Integration Test — Section 2 of 2';

export const ANIMATION = {
  // Frame 0-8: Circle draws itself (strokeDashoffset, clockwise from top)
  circleDrawStart: 0,
  circleDrawEnd: 8,
  // Frame 8-16: Check stroke draws inside circle; circle fills with green tint
  checkDrawStart: 8,
  checkDrawEnd: 16,
  // Frame 16-22: Completion text fades in + slides up 15px; rule expands
  textFadeStart: 16,
  textFadeEnd: 22,
  textSlideY: 15,
  // Frame 22-28: Tagline fades in (opacity 0 → 0.7)
  taglineFadeStart: 22,
  taglineFadeEnd: 28,
  // Frame 28-37: Fade to black overlay (opacity 0 → 1)
  fadeToBlackStart: 28,
  fadeToBlackEnd: 37,
  totalDuration: 37,
} as const;
