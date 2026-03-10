// Component-level constants for AnimationSection03BlueCirclePulse

export const CANVAS = {
  width: 1920,
  height: 1080,
  centerX: 960,
  centerY: 540,
};

export const COLORS = {
  background: '#0F172A',
  circleFill: '#EC4899',
  rippleStroke: '#F472B6',
  vignette: 'rgba(0,0,0,0.3)',
};

export const CIRCLE = {
  radius: 80,
  diameter: 160,
  pulseRadius: 90,
  pulseDiameter: 180,
};

export const GLOW = {
  radius: 100,
  diameter: 200,
  opacity: 0.25,
  blur: 40,
};

export const RIPPLE = {
  startRadius: 90,
  endRadius: 200,
  strokeWidth: 2,
  startOpacity: 0.6,
};

export const ANIMATION_TIMING = {
  // Frame 0-15: Circle scales from 0 to full, opacity 0→1
  scaleInStart: 0,
  scaleInEnd: 15,
  // Frame 15-25: Hold at full size
  holdStart: 15,
  holdEnd: 25,
  // Frame 25-35: Pulse — scale up to 180px then back to 160px
  pulseStart: 25,
  pulsePeak: 30,
  pulseEnd: 35,
  // Frame 35-50: Ripple ring expands and fades
  rippleStart: 35,
  rippleEnd: 50,
  // Frame 35-60: Subtle breathing
  breathingStart: 35,
  breathingEnd: 60,
  totalDuration: 60,
};
