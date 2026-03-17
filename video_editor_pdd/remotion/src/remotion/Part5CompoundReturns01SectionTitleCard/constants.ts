// Color palette
export const COLORS = {
  background: '#0A0F1A',
  gridLine: '#1E293B',
  titleText: '#E2E8F0',
  sectionLabel: '#64748B',
  rule: '#334155',
  amberCurve: '#D9944A',
  blueCurve: '#4A90D9',
  originDot: '#E2E8F0',
} as const;

// Canvas dimensions
export const CANVAS = {
  width: 1920,
  height: 1080,
} as const;

// Grid settings
export const GRID = {
  hSpacing: 40,
  vAccentEvery: 120,
  hOpacity: 0.04,
  vOpacity: 0.06,
} as const;

// Layout positions
export const LAYOUT = {
  sectionLabelY: 400,
  titleLine1Y: 460,
  ruleY: 505,
  titleLine2Y: 545,
  titleLine2OffsetX: 15,
  ruleHalfWidth: 100,
  centerX: 960,
} as const;

// Curve geometry
export const CURVES = {
  origin: { x: 960, y: 520 },
  amberEnd: { x: 1300, y: 350 },
  blueEnd: { x: 1300, y: 550 },
  strokeWidth: 2,
  opacity: 0.04,
  glowBlur: 8,
  glowOpacity: 0.02,
  originDotRadius: 4,
  originDotOpacity: 0.03,
} as const;

// Animation timing (in frames)
export const TIMING = {
  bgFadeEnd: 15,
  part5FadeStart: 15,
  curvesDrawStart: 15,
  curvesDrawDuration: 60,
  compoundTypeStart: 40,
  charDelay: 3,
  ruleDrawStart: 60,
  ruleDrawDuration: 10,
  returnsFadeStart: 70,
  returnsFadeDuration: 20,
  returnsSlideDistance: 10,
  textFadeDuration: 20,
  pulseCycleFrames: 30,
  holdStart: 90,
  totalFrames: 120,
} as const;
