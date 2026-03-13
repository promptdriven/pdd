// Component-level constants for AnimationSection02BlueCirclePulse

export const CANVAS = {
  width: 1920,
  height: 1080,
  centerX: 960,
  centerY: 540,
} as const;

export const COLORS = {
  backgroundCenter: '#1E293B',
  backgroundEdge: '#0F172A',
  circleFill: '#3B82F6',
  glowColor: 'rgba(59, 130, 246, 0.2)',
} as const;

export const CIRCLE = {
  baseRadius: 60,
  pulseRadius: 80,
  glowRadius: 120,
} as const;

export const TIMING = {
  // Phase 1 (frames 0-5): Circle appears, scaling from 0 to baseRadius
  appearStart: 0,
  appearEnd: 5,

  // Phase 2 (frames 5-15): First pulse — expand to pulseRadius, glow expands
  pulse1Start: 5,
  pulse1End: 15,

  // Phase 3 (frames 15-20): Contract back to baseRadius, glow fades
  contract1Start: 15,
  contract1End: 20,

  // Phase 4 (frames 20-28): Second pulse — same expansion pattern
  pulse2Start: 20,
  pulse2End: 28,

  // Phase 5 (frames 28-30): Hold at baseRadius
  holdStart: 28,
  holdEnd: 30,

  totalDuration: 30,
} as const;
