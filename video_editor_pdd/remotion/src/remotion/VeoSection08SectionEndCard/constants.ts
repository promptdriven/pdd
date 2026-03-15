// Component-level constants for VeoSection08SectionEndCard
// Duration: ~1.7s (51 frames @ 30fps)

export const CANVAS = {
  width: 1920,
  height: 1080,
} as const;

export const COLORS = {
  background: '#0B1120',
  fadeTarget: '#000000',
  accent: '#C9A84C',
  accentFaint: 'rgba(201, 168, 76, 0.4)',
  text: '#FFFFFF',
  glow: '#C9A84C',
} as const;

export const CHECKMARK = {
  cx: 960,
  cy: 420,
  size: 64,
  strokeWidth: 3,
  viewBoxSize: 64,
  circleRadius: 30,
  glowBlur: 24,
  glowOpacity: 0.25,
} as const;

/**
 * Checkmark SVG path within a 64x64 viewBox.
 * Short downstroke then long upstroke, centered in the viewBox.
 */
export const CHECKMARK_PATH = 'M 18 32 L 28 42 L 46 22';

// Circle circumference for stroke-draw: 2 * PI * radius
export const CIRCLE_CIRCUMFERENCE = 2 * Math.PI * CHECKMARK.circleRadius;

// Checkmark path total length (approximate):
// Seg1: (18,32)->(28,42) = sqrt(10^2+10^2) ~ 14.1
// Seg2: (28,42)->(46,22) = sqrt(18^2+20^2) ~ 26.9
// Total ~ 41
export const CHECKMARK_PATH_LENGTH = 41;

export const TEXT = {
  content: 'Veo Section Complete',
  y: 520,
  fontSize: 36,
  fontWeight: 600 as const,
  fontFamily: "'Inter', sans-serif",
  translateY: 16,
} as const;

export const RULE = {
  y: 570,
  maxWidth: 240,
  height: 2,
} as const;

export const TIMING = {
  fps: 30,
  totalFrames: 51,
  // Frames 0-6: Background crossfade to #0B1120
  crossfadeEnd: 6,
  // Frames 6-16: Checkmark draws (circle first, then check path)
  checkmarkStart: 6,
  checkmarkEnd: 16,
  // Circle draws in first portion of checkmark window (frames 6-12)
  circleSplitFrame: 12,
  // Frames 16-24: Text fades in + translates up
  textStart: 16,
  textEnd: 24,
  // Frames 24-30: Rule expands from center
  ruleStart: 24,
  ruleEnd: 30,
  // Frames 41-51: Final fade to black
  fadeStart: 41,
  fadeEnd: 51,
} as const;
