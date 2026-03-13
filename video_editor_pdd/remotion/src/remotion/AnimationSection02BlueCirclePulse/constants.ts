// Component-level constants for AnimationSection02BlueCirclePulse

export const CANVAS = {
  width: 1280,
  height: 720,
} as const;

export const COLORS = {
  background: '#141921',
  triangle: '#3B82F6',
  dropShadow: 'rgba(59, 130, 246, 0.3)',
} as const;

export const DIMENSIONS = {
  /** Side length / bounding box of the equilateral triangle */
  triangleSize: 180,
  glowMinDiameter: 220,
  glowMaxDiameter: 280,
  glowBlur: 30,
} as const;

export const TIMING = {
  // Phase 1: Spring scale-in with overshoot (frames 0-8)
  springStart: 0,
  springEnd: 8,

  // Phase 2: Settle + glow/shadow fade in (frames 8-15)
  settleStart: 8,
  settleEnd: 15,

  // Phase 3: Pulse beat (frames 15-28)
  pulseStart: 15,
  pulsePeak: 21,
  pulseEnd: 28,

  // Phase 4: Breathing rest (frames 28-45)
  breathingStart: 28,
  breathingEnd: 45,
  breathingCycleFrames: 15,

  totalDuration: 45,
} as const;

export const PULSE = {
  overshootScale: 1.08,
  peakScale: 1.15,
  breathingScale: 1.02,
  glowOpacity: 0.15,
  breathingOpacityMin: 0.12,
  breathingOpacityMax: 0.18,
} as const;
