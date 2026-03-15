// AnimationSection09SplitSummary – visual constants
// Authoritative data contract for the split summary card

export const CANVAS = {
  width: 1920,
  height: 1080,
  background: '#020617',
} as const;

export const DIVIDER = {
  startX: 640,
  endX: 720,
  color: '#38BDF8',
  width: 3,
  glowBlur: 24,
  glowOpacity: 0.3,
  glowWidth: 20,
} as const;

export const COLORS = {
  leftBackground: '#0F172A',
  leftOpacity: 0.9,
  rightBackground: '#020617',
  rightOpacity: 1.0,
  labelColor: '#FFFFFF',
  labelOpacity: 0.7,
} as const;

export const LABEL = {
  text: 'Split Summary',
  x: 80,
  y: 60,
} as const;

export const TYPOGRAPHY = {
  label: {
    fontFamily: 'Inter, sans-serif',
    fontSize: 20,
    fontWeight: 600 as const,
  },
} as const;

export const TIMING = {
  // Frame 0-6: Card fades in (opacity 0→1)
  fadeInStart: 0,
  fadeInEnd: 6,
  // Frame 6-18: Divider drifts from startX to endX
  driftStart: 6,
  driftEnd: 18,
  // Frame 18-22: Label fades in, divider settles
  labelFadeStart: 18,
  labelFadeEnd: 22,
  totalFrames: 22,
} as const;
