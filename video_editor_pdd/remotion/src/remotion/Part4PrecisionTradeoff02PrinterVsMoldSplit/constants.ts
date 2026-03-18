// === Colors ===
export const COLORS = {
  // Backgrounds
  sceneBg: '#000000',
  leftPanelBg: '#0F172A',
  rightPanelBg: '#0A0F1A',

  // Split divider
  splitLine: '#334155',

  // Left panel (3D Printing)
  leftHeader: '#94A3B8',
  gridLine: '#1E293B',
  gridDot: '#334155',
  activeDot: '#4A90D9',
  nozzle: '#E2E8F0',
  leftAnnotation: '#64748B',

  // Right panel (Injection Molding)
  rightHeader: '#D9944A',
  wallColor: '#D9944A',
  fluidColor: '#4A90D9',
  moldNozzle: '#94A3B8',
  rightAnnotation: '#D9944A',

  // Bottom callout
  calloutText: '#E2E8F0',
  calloutSpec: '#94A3B8',
  calloutConstraint: '#D9944A',
} as const;

// === Layout ===
export const LAYOUT = {
  width: 1920,
  height: 1080,
  splitX: 960,
  splitLineWidth: 2,

  leftPanelX: 0,
  leftPanelWidth: 958,
  rightPanelX: 962,
  rightPanelWidth: 958,

  headerY: 40,
  counterY: 900,
  annotationY: 930,
  calloutY: 980,
} as const;

// === Grid ===
export const GRID = {
  rows: 20,
  cols: 20,
  spacing: 36,
  // Center of left panel
  centerX: 479,
  centerY: 460,
  dotRadius: 3,
  activeDotRadius: 5,
  totalPoints: 400,
} as const;

// === Mold ===
export const MOLD = {
  width: 400,
  height: 500,
  wallWidth: 6,
  // Center of right panel (relative to right panel)
  centerX: 479,
  centerY: 460,
} as const;

// === Timing (frames) ===
export const TIMING = {
  // Phase 1: Split line + headers
  splitStart: 0,
  splitDuration: 15,
  headerFadeStart: 5,
  headerFadeDuration: 15,

  // Phase 2: Grid + Mold walls appear
  gridAppearStart: 20,
  gridAppearDuration: 40,
  moldWallDrawStart: 20,
  moldWallDrawDuration: 30,

  // Phase 3-6: Nozzle traversal + fluid fill
  nozzleStart: 60,
  nozzleEnd: 460,
  nozzleDuration: 400, // frames 60-460
  fluidStart: 60,
  fluidEnd: 460,
  fluidDuration: 400,

  // Phase 7: Hold
  holdStart: 480,
  holdEnd: 540,

  // Phase 8: Callout
  calloutFadeStart: 540,
  calloutFadeDuration: 20,

  totalFrames: 600,
} as const;

// === Typography ===
export const FONT = {
  family: 'Inter, sans-serif',
  headerSize: 14,
  headerWeight: 600 as const,
  headerLetterSpacing: 2,
  counterSize: 14,
  annotationSize: 11,
  calloutSize: 14,
} as const;
