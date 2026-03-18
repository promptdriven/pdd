// Part 4 Title Card — The Precision Tradeoff
// Component-level constants

export const CANVAS = {
  WIDTH: 1920,
  HEIGHT: 1080,
  FPS: 30,
  DURATION_FRAMES: 120,
} as const;

export const COLORS = {
  background: '#0A0F1A',
  blueprintGrid: '#1E293B',
  sectionLabel: '#64748B',
  titleText: '#E2E8F0',
  rule: '#334155',
  dotGrid: '#94A3B8',
  moldOutline: '#D9944A',
} as const;

export const OPACITIES = {
  blueprintGrid: 0.05,
  sectionLabel: 0.5,
  rule: 0.5,
  ghostDots: 0.03,
  ghostMold: 0.04,
  ghostLabel: 0.03,
  ghostGlow: 0.02,
} as const;

export const TYPOGRAPHY = {
  sectionLabel: {
    size: 14,
    weight: 600,
    letterSpacing: 4,
  },
  title: {
    size: 72,
    weight: 700,
  },
  ghostLabel: {
    size: 8,
  },
} as const;

export const POSITIONS = {
  sectionLabel: { x: 960, y: 400 },
  titleLine1: { x: 960, y: 460 },
  titleLine2: { x: 975, y: 545 },
  rule: { y: 505, halfWidth: 100 },
  dotGrid: { x: 560, y: 480 },
  moldOutline: { x: 1360, y: 480 },
} as const;

export const DOT_GRID = {
  rows: 8,
  cols: 8,
  dotSize: 4,
  spacing: 12,
} as const;

export const MOLD = {
  width: 100,
  height: 80,
  strokeWidth: 3,
} as const;

export const TIMING = {
  // Phase 1: Background + grid (0-15)
  bgFadeEnd: 15,
  // Phase 2: PART 4 label + ghost shapes (15-40)
  ghostStart: 15,
  labelFadeStart: 15,
  labelFadeDuration: 20,
  // Phase 3: THE PRECISION typewriter (40-60)
  typewriterStart: 40,
  charDelay: 3, // frames per character
  // Phase 4: Horizontal rule (60-70)
  ruleStart: 60,
  ruleDuration: 10,
  // Phase 5: TRADEOFF fade + slide (70-90)
  tradeoffStart: 70,
  tradeoffDuration: 20,
  tradeoffSlideDistance: 10,
  // Phase 6: Hold + pulse (90-120)
  holdStart: 90,
  pulseCycleFrames: 30,
  // Ghost animation
  wallDrawDuration: 40,
  glowBlur: 8,
} as const;
