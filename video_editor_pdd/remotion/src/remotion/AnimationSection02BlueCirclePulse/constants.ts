// Component-level constants for AnimationSection02BlueCirclePulse

export const CANVAS = {
  width: 1280,
  height: 720,
};

export const COLORS = {
  background: '#141921',
  circle: '#3B82F6',
  dropShadow: 'rgba(59, 130, 246, 0.3)',
};

export const DIMENSIONS = {
  circleDiameter: 180,
  glowDiameter: 220,
  glowExpandedDiameter: 280,
  glowBlur: 30,
};

export const TIMING = {
  // Frame 0-20: Circle scales in with spring overshoot
  scaleInStart: 0,
  scaleInEnd: 20,
  // Frame 20-50: Hold steady, glow fades in
  holdStart: 20,
  glowFadeEnd: 50,
  // Frame 50-75: Pulse beat
  pulseStart: 50,
  pulseMid: 62,
  pulseEnd: 75,
  // Frame 75-120: Rest with gentle glow oscillation
  restStart: 75,
  totalDuration: 120,
};

export const PULSE = {
  peakScale: 1.15,
  glowOpacityMin: 0.15,
  glowOpacityMax: 0.25,
  glowOpacityPeak: 0.4,
  glowOpacityRest: 0.2,
};
