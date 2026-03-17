// constants.ts — Component-level constants for Research Annotations AI Quality

export const CANVAS = {
  WIDTH: 1920,
  HEIGHT: 1080,
  BG: '#0A0F1A',
} as const;

export const COLORS = {
  cardBg: '#1E293B',
  red: '#EF4444',
  green: '#5AAA6E',
  amber: '#D9944A',
  label: '#64748B',
  white: '#FFFFFF',
} as const;

export const FONTS = {
  family: 'Inter, system-ui, sans-serif',
} as const;

// Frame-based animation timing
export const TIMING = {
  // Phase 1: Mold dims
  moldDimStart: 0,
  moldDimEnd: 30,
  // Phase 2: Card 1 materializes
  card1Start: 30,
  card1BorderDraw: 20,
  card1BgFade: 15,
  card1StatStart: 55,
  card1SubStatStart: 75,
  card1SubStatDelay: 15,
  // Phase 3: Card 2 materializes
  card2Start: 120,
  card2StatStart: 145,
  card2ArrowStart: 180,
  card2ArrowDraw: 25,
  // Phase 4: Visual equation
  equationStart: 210,
  equationLeftDur: 20,
  equationVsDelay: 25,
  equationRightDelay: 50,
  equationBracketDelay: 70,
  // Phase 5: Wall pulse
  wallPulseStart: 330,
  wallPulseDur: 60,
  // Phase 6: Hold
  holdStart: 390,
  totalFrames: 450,
} as const;

// Mold cross-section geometry
export const MOLD = {
  centerX: 960,
  centerY: 500,
  outerWidth: 600,
  outerHeight: 300,
  wallThickness: 30,
  innerWidth: 540,
  innerHeight: 240,
} as const;

// Wall pulse triggers (frames where mold walls pulse)
export const WALL_PULSE_TRIGGERS = [55, 75, 90, 145, 330] as const;
