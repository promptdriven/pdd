// Component-level constants for AnimationSection02BlueCirclePulse

export const CANVAS = {
  width: 1920,
  height: 1080,
  centerX: 960,
  centerY: 540,
} as const;

export const COLORS = {
  backgroundCenter: '#0F172A',
  backgroundEdge: '#020617',
  circleFill: '#3B82F6',
} as const;

export const CIRCLE = {
  baseRadius: 60,
  pulse1Radius: 80,
  pulse2Radius: 78,
  glowOffsetRadius: 20,
  glowBlur: 30,
} as const;

export const TIMING = {
  // Phase 1 (frames 0-5): Circle fades in, radius 60px, opacity 0→1
  fadeInStart: 0,
  fadeInEnd: 5,

  // Phase 2 (frames 5-12): First pulse expand — radius 60→80px, glow brightens to 40%
  pulse1ExpandStart: 5,
  pulse1ExpandEnd: 12,

  // Phase 3 (frames 12-18): First pulse contract — radius 80→60px, glow fades to 15%
  pulse1ContractStart: 12,
  pulse1ContractEnd: 18,

  // Phase 4 (frames 18-24): Second pulse expand — radius 60→78px, glow brightens to 35%
  pulse2ExpandStart: 18,
  pulse2ExpandEnd: 24,

  // Phase 5 (frames 24-30): Second pulse contract — radius 78→60px, glow settles at 20%
  pulse2ContractStart: 24,
  pulse2ContractEnd: 30,

  totalDuration: 30,
} as const;

export const GLOW_OPACITY = {
  initial: 0,
  afterFadeIn: 0.25,
  pulse1Peak: 0.40,
  afterPulse1: 0.15,
  pulse2Peak: 0.35,
  final: 0.20,
} as const;
