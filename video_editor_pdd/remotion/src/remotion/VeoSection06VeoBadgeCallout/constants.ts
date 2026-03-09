// Component-level constants for VeoSection06VeoBadgeCallout
// Floating "Powered by Veo" badge pill — upper-right overlay

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: 'transparent',
  badgeBg: 'rgba(0, 0, 0, 0.7)',
  badgeBorder: 'rgba(245, 158, 11, 0.4)',
  badgeText: '#F59E0B',
  sparkleIcon: '#F59E0B',
  dropShadow: '0 2px 8px rgba(0, 0, 0, 0.3)',
};

export const TYPOGRAPHY = {
  badge: {
    fontSize: 14,
    fontFamily: 'Inter',
    fontWeight: 600 as const,
    letterSpacing: '0.5px',
  },
};

export const POSITIONS = {
  badgeRestX: 1680,
  badgeOffscreenX: 1960,
  badgeY: 60,
};

export const DIMENSIONS = {
  badgeWidth: 200,
  badgeHeight: 44,
  badgeBorderRadius: 24,
  sparkleSize: 16,
};

export const ANIMATION = {
  // Slide in: frames 0-15
  slideInStart: 0,
  slideInEnd: 15,

  // Sparkle rotation: frames 15-20
  sparkleRotateStart: 15,
  sparkleRotateEnd: 20,

  // Breathing hold: frames 20-75
  breathingStart: 20,
  breathingEnd: 75,
  breathingCycleDuration: 60, // frames per full breathing cycle

  // Scale breathing range
  breathingScaleMin: 1.0,
  breathingScaleMax: 1.03,

  // Slide out: frames 75-90
  slideOutStart: 75,
  slideOutEnd: 90,

  totalDuration: 90,
};

export const BADGE_TEXT = 'Powered by Veo';
