// Component-level constants for AnimationSection02IntroDataPulse

export const CANVAS = {
  width: 1920,
  height: 1080,
  centerX: 960,
  centerY: 540,
};

export const COLORS = {
  background: '#0F172A',
  centralDot: '#60A5FA',
  ring1: '#3B82F6',
  ring2: '#06B6D4',
  ring3: '#22D3EE',
  radialLine: '#1E293B',
  labelText: '#94A3B8',
};

export const RINGS = [
  { radius: 120, color: '#3B82F6', opacity: 0.8, startFrame: 10, endFrame: 30 },
  { radius: 240, color: '#06B6D4', opacity: 0.6, startFrame: 20, endFrame: 45 },
  { radius: 360, color: '#22D3EE', opacity: 0.4, startFrame: 30, endFrame: 55 },
];

export const CENTRAL_DOT = {
  baseRadius: 6,
  minScale: 0.67,   // 8px / 12px
  maxScale: 1.33,   // 16px / 12px
  color: COLORS.centralDot,
  glowRadius: 20,
  fadeInEnd: 15,
};

export const RADIAL_LINES = {
  count: 8,
  maxRadius: 360,
  opacity: 0.15,
  strokeWidth: 1,
  color: COLORS.radialLine,
};

export const ORBIT_LABELS = {
  labels: ['Section 1', 'Remotion', '30fps'],
  radius: 360,
  fontSize: 18,
  fontFamily: 'Inter',
  color: COLORS.labelText,
  fadeInStart: 40,
  fadeInEnd: 55,
  rotationSpeed: 0.5, // degrees per frame
};

export const ANIMATION = {
  totalDuration: 75,
};
