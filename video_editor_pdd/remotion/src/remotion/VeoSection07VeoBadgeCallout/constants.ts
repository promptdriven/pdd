// Component-level constants for VeoSection07VeoBadgeCallout

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: 'transparent',
  gradientFrom: 'transparent',
  gradientTo: '#000000AA',
  badgeBg: '#0F172BCC',
  badgeBorder: '#3B82F650',
  badgeGlow: '#3B82F630',
  badgeText: '#3B82F6',
  badgeIcon: '#3B82F6',
  subtitleText: '#FFFFFF',
  progressBar: '#3B82F6',
  progressBarTrack: '#1E293B80',
};

export const TYPOGRAPHY = {
  badge: {
    fontSize: 14,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 700 as const,
    letterSpacing: '2.5px',
    textTransform: 'uppercase' as const,
  },
  subtitle: {
    fontSize: 28,
    fontFamily: 'Inter, sans-serif',
    fontWeight: 400 as const,
    letterSpacing: '0.4px',
    lineHeight: 1.5,
  },
};

export const POSITIONS = {
  badgeX: 120,
  badgeY: 860,
  subtitleX: 120,
  subtitleY: 920,
  progressBarY: 1074,
};

export const DIMENSIONS = {
  gradientBarHeight: 220,
  badgeWidth: 200,
  badgeHeight: 38,
  badgeBorderRadius: 19,
  progressBarHeight: 6,
  progressBarBorderRadius: 3,
  subtitleMaxWidth: 1400,
  iconSize: 14,
};

export const ANIMATION = {
  // Gradient bar: instant at frame 0, full opacity by frame 8
  gradientFadeStart: 0,
  gradientFadeEnd: 8,
  gradientMaxOpacity: 0.9,

  // Badge scale-in: frames 0-16
  badgeScaleStart: 0,
  badgeScaleDuration: 16,

  // Badge glow pulse: continuous after badge appears
  badgeGlowCycleFrames: 40,
  badgeGlowMinOpacity: 0.3,
  badgeGlowMaxOpacity: 0.8,

  // Subtitle type-on: frames 12-55
  subtitleTypeStart: 12,
  charsPerFrame: 1.2,

  // Progress bar: frames 8-80
  progressStart: 8,
  progressDuration: 72,

  // Fade out: frames 80-90
  fadeOutStart: 80,
  fadeOutEnd: 90,

  totalDuration: 90,
};

export const NARRATION_TEXT = 'Side-by-side comparison powered by Veo AI generation.';
export const BADGE_LABEL = 'VEO AI';
