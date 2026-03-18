// === Colors ===
export const COLORS = {
  background: '#0A0F1A',
  cardBg: '#1E293B',
  red: '#EF4444',
  green: '#5AAA6E',
  amber: '#D9944A',
  muted: '#64748B',
  white: '#FFFFFF',
  moldWall: '#D9944A',
  moldCavity: '#1A1A2E',
} as const;

// === Dimensions ===
export const CANVAS = {
  width: 1920,
  height: 1080,
} as const;

// === Card positions & sizes ===
export const CARD1 = {
  x: 200,
  y: 200,
  width: 400,
  height: 220,
} as const;

export const CARD2 = {
  x: 1320,
  y: 200,
  width: 400,
  height: 180,
} as const;

// === Animation timing (in frames @ 30fps) ===
export const TIMING = {
  // Phase 1: Mold dims
  moldDimStart: 0,
  moldDimEnd: 30,

  // Phase 2: Card 1 materializes
  card1Start: 30,
  card1BorderDraw: 20,
  card1BgFade: 15,
  card1HeaderType: 15,
  card1MainStatStart: 50,
  card1SubStat1Start: 75,
  card1SubStat2Start: 90,

  // Phase 3: Card 2 materializes
  card2Start: 120,
  card2MainStatStart: 150,
  card2ArrowStart: 180,
  card2ArrowDuration: 25,

  // Phase 4: Visual equation
  equationStart: 210,
  equationLeftDuration: 20,
  equationVsStart: 240,
  equationRightStart: 260,
  equationBracketStart: 290,

  // Phase 5: Wall pulse intensify
  wallPulseStart: 330,
  wallPulseEnd: 390,

  // Phase 6: Hold
  holdStart: 390,
  totalFrames: 450,
} as const;

// === Mold wall pulse triggers ===
export const WALL_PULSE_TRIGGERS = [30, 75, 90, 120, 210, 330] as const;

// === Typography ===
export const FONT = {
  family: 'Inter, sans-serif',
} as const;
