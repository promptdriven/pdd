// Component-level constants for VeoSection09SectionOutro

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  gradientTop: '#0A1A1F',
  gradientBottom: '#0F2027',
  checkmark: '#34D399',
  checkmarkBorder: 'rgba(52, 211, 153, 0.37)',
  checkmarkBg: 'rgba(52, 211, 153, 0.08)',
  statusText: '#94A3B8',
  particleColor1: '#D4A574',
  particleColor2: '#F59E0B',
  filmGrain: '#FFFFFF',
};

export const TYPOGRAPHY = {
  status: {
    fontSize: 24,
    fontFamily: 'Inter',
    fontWeight: 400 as const,
    letterSpacing: '1.5px',
    textTransform: 'uppercase' as const,
  },
};

export const POSITIONS = {
  checkmarkCy: 460,
  statusTextY: 540,
};

export const DIMENSIONS = {
  checkmarkCircleSize: 60,
  checkmarkStrokeWidth: 3,
  checkmarkBorderWidth: 2,
};

export const ANIMATION_TIMING = {
  // Background crossfade: frames 0-8
  crossfadeStart: 0,
  crossfadeEnd: 8,
  // Checkmark circle + stroke draw: frames 8-22
  checkmarkFadeStart: 8,
  checkmarkFadeEnd: 14,
  checkmarkDrawStart: 8,
  checkmarkDrawEnd: 22,
  // Checkmark pulse: frames 18-22
  pulseStart: 18,
  pulseEnd: 22,
  // Status text fade-in: frames 22-34
  textFadeStart: 22,
  textFadeEnd: 34,
  // Fade to black: frames 34-42
  fadeOutStart: 34,
  fadeOutEnd: 42,
  totalDuration: 42,
};

export const PARTICLES = {
  count: 15,
  minRadius: 4,
  maxRadius: 14,
  driftSpeed: 0.3,
  opacityMin: 0.04,
  opacityMax: 0.12,
};
