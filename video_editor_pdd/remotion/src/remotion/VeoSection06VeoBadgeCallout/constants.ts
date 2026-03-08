// Component-level constants for VeoSection06VeoBadgeCallout

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: 'transparent',
  gradientFrom: 'transparent',
  gradientTo: '#00000088',
  badgeBg: '#1E293B99',
  badgeBorder: '#22C55E40',
  badgeText: '#22C55E',
  badgeIcon: '#22C55E',
  subtitleText: '#FFFFFF',
  progressBar: '#22C55E',
};

export const TYPOGRAPHY = {
  badge: {
    fontSize: 14,
    fontFamily: 'Inter',
    fontWeight: 600 as const,
    letterSpacing: '2px',
    textTransform: 'uppercase' as const,
  },
  subtitle: {
    fontSize: 30,
    fontFamily: 'Inter',
    fontWeight: 400 as const,
    letterSpacing: '0.3px',
  },
};

export const POSITIONS = {
  badgeX: 120,
  badgeY: 870,
  subtitleX: 120,
  subtitleY: 930,
  progressBarY: 1076,
};

export const DIMENSIONS = {
  gradientBarHeight: 180,
  badgeWidth: 220,
  badgeHeight: 40,
  badgeBorderRadius: 20,
  progressBarHeight: 4,
  subtitleMaxWidth: 1400,
  playIconSize: 8,
};

export const ANIMATION = {
  // Gradient bar fade in: frames 0-10
  gradientFadeStart: 0,
  gradientFadeEnd: 10,
  gradientMaxOpacity: 0.85,

  // Badge slide in: frames 8-22
  badgeSlideStart: 8,
  badgeSlideDistance: 340, // from -220 → 120

  // Subtitle type-on: frames 15-55
  subtitleTypeStart: 15,
  charsPerFrame: 1.3,

  // Progress bar: frames 10-80
  progressStart: 10,
  progressDuration: 70,

  // Fade out: frames 80-90
  fadeOutStart: 80,
  fadeOutEnd: 90,

  totalDuration: 90,
};

export const NARRATION_TEXT = 'It uses Veo-generated clips with narration overlay.';
export const BADGE_LABEL = 'VEO GENERATED';
