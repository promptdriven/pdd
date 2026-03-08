// Component-level constants for AnimationSection08ClosingBadge

export const CANVAS = {
  width: 1920,
  height: 1080,
};

export const COLORS = {
  background: '#0F172A',
  spotlightColor: 'rgba(59, 130, 246, 0.08)',
  strokeColor: '#3B82F6',
  gradientStart: '#3B82F6',
  gradientEnd: '#06B6D4',
  textColor: '#E2E8F0',
  glowColor: '#3B82F6',
};

export const POSITIONS = {
  monogramCenterX: 960,
  monogramCenterY: 400,
  textCenterY: 600,
};

export const DIMENSIONS = {
  monogramHeight: 200,
  ringDiameter: 260,
  ringRadius: 130,
  strokeWidth: 3,
  glowBlurRadius: 30,
  glowOpacity: 0.2,
};

export const TYPOGRAPHY = {
  brandName: {
    fontFamily: 'Inter, sans-serif',
    fontSize: 40,
    fontWeight: 600 as const,
    letterSpacing: '4px',
  },
};

export const ANIMATION_TIMING = {
  // Stroke draw: frame 0-25
  strokeDrawStart: 0,
  strokeDrawEnd: 25,
  // Progress ring: frame 12-35
  ringStart: 12,
  ringEnd: 35,
  // Monogram fill: frame 20-30
  fillStart: 20,
  fillEnd: 30,
  // Typewriter: frame 25-45 (3 frames per char, 7 chars = 21 frames)
  typewriterStart: 25,
  charInterval: 3,
  // Glow pulse: frame 40-55
  glowPulseStart: 40,
  glowPulseEnd: 55,
  // Total duration
  totalDuration: 60,
};

// SVG path for stylized "R" monogram — a clean geometric R
// Viewbox: 0 0 120 160
export const MONOGRAM_R_PATH =
  'M 20 150 L 20 10 L 70 10 Q 100 10 100 45 Q 100 80 70 80 L 50 80 L 100 150';

export const MONOGRAM_VIEWBOX = '0 0 120 160';
