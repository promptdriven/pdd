// Component-level constants for AnimationSection02BlueCirclePulse

export const CANVAS = {
  width: 1920,
  height: 1080,
  centerX: 960,
  centerY: 540,
};

export const COLORS = {
  background: '#111827',
  circleFill: '#3B82F6',
  glowColor: 'rgba(59, 130, 246, 0.5)',
  pulseRingColor: '#3B82F6',
};

export const CIRCLE = {
  radius: 100,
  diameter: 200,
};

export const PULSE = {
  scaleMax: 1.15,
  ringStartRadius: 100,
  ringEndRadius: 150,
  ringStartOpacity: 0.3,
};

export const TIMING = {
  // Frame 0-20: Circle scales from 0 to 1.0, opacity 0→100%
  scaleInStart: 0,
  scaleInEnd: 20,
  // Frame 20-40: Hold at full size, drop shadow fades in
  holdStart: 20,
  holdEnd: 40,
  // Frame 40-60: Pulse — scale 1.0→1.15→1.0, pulse ring expands
  pulseStart: 40,
  pulsePeak: 50,
  pulseEnd: 60,
  // Frame 60-90: Hold steady
  steadyStart: 60,
  steadyEnd: 90,
  // Frame 90-150: Remain on screen
  totalDuration: 150,
};
