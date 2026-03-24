// constants.ts — Dissolve-Regenerate Loop visual constants

export const CANVAS = {
  width: 1920,
  height: 1080,
  backgroundColor: '#0A0F1A',
} as const;

export const RADIAL_GLOW = {
  cx: 960,
  cy: 520,
  radius: 600,
  color: '#1E293B',
  opacity: 0.04,
} as const;

// Equilateral triangle centered at (960, 520), side ~500px
export const TRIANGLE = {
  vertices: [
    [960, 280],
    [710, 713],
    [1210, 713],
  ] as [number, number][],
  center: [960, 520] as [number, number],
  edgeColor: '#334155',
  edgeOpacity: 0.3,
  edgeWidth: 2,
  glowBlur: 4,
  glowOpacity: 0.15,
} as const;

export const NODES = [
  { center: [960, 280] as [number, number], fill: '#60A5FA', label: 'PROMPT' },
  { center: [710, 713] as [number, number], fill: '#4ADE80', label: 'TESTS' },
  { center: [1210, 713] as [number, number], fill: '#D9944A', label: 'GROUNDING' },
] as const;

export const NODE_RADIUS = 20;
export const NODE_PULSE_MIN = 20;
export const NODE_PULSE_MAX = 22;
export const NODE_PULSE_PERIOD = 60;

export const CODE_COLOR = '#94A3B8';
export const CODE_OPACITY = 0.15;

// Each code pattern is an array of { width, offsetX, offsetY } for horizontal lines
export const CODE_PATTERNS = [
  // Pattern 1 — initial code
  [
    { width: 140, offsetX: -30, offsetY: -60 },
    { width: 100, offsetX: 10, offsetY: -42 },
    { width: 170, offsetX: -20, offsetY: -24 },
    { width: 80, offsetX: 30, offsetY: -6 },
    { width: 130, offsetX: -10, offsetY: 12 },
    { width: 60, offsetX: 20, offsetY: 30 },
    { width: 150, offsetX: -25, offsetY: 48 },
    { width: 110, offsetX: 5, offsetY: 66 },
  ],
  // Pattern 2
  [
    { width: 90, offsetX: 15, offsetY: -54 },
    { width: 160, offsetX: -35, offsetY: -36 },
    { width: 70, offsetX: 25, offsetY: -18 },
    { width: 180, offsetX: -15, offsetY: 0 },
    { width: 120, offsetX: 5, offsetY: 18 },
    { width: 60, offsetX: -20, offsetY: 36 },
    { width: 140, offsetX: 10, offsetY: 54 },
    { width: 100, offsetX: -5, offsetY: 72 },
    { width: 80, offsetX: 30, offsetY: 90 },
  ],
  // Pattern 3
  [
    { width: 120, offsetX: -10, offsetY: -48 },
    { width: 80, offsetX: 20, offsetY: -30 },
    { width: 150, offsetX: -25, offsetY: -12 },
    { width: 60, offsetX: 35, offsetY: 6 },
    { width: 170, offsetX: -30, offsetY: 24 },
    { width: 100, offsetX: 0, offsetY: 42 },
    { width: 90, offsetX: 15, offsetY: 60 },
  ],
  // Pattern 4 — final
  [
    { width: 110, offsetX: -5, offsetY: -56 },
    { width: 160, offsetX: -20, offsetY: -38 },
    { width: 70, offsetX: 30, offsetY: -20 },
    { width: 130, offsetX: -15, offsetY: -2 },
    { width: 90, offsetX: 10, offsetY: 16 },
    { width: 180, offsetX: -30, offsetY: 34 },
    { width: 60, offsetX: 25, offsetY: 52 },
    { width: 140, offsetX: -10, offsetY: 70 },
    { width: 100, offsetX: 5, offsetY: 88 },
    { width: 80, offsetX: 20, offsetY: 106 },
  ],
] as const;

// Dissolve-regenerate cycle timings
export const CYCLES = [
  {
    // Cycle 1 — slow
    dissolveStart: 10,
    dissolveDuration: 30,
    regenerateStart: 40,
    regenerateDuration: 30,
    patternFrom: 0, // dissolves pattern 0
    patternTo: 1,   // regenerates pattern 1
    particlesPerLine: 6,
    driftRadius: 120,
    fadeDuration: 15,
    stagger: 6,
  },
  {
    // Cycle 2 — medium
    dissolveStart: 70,
    dissolveDuration: 25,
    regenerateStart: 95,
    regenerateDuration: 25,
    patternFrom: 1,
    patternTo: 2,
    particlesPerLine: 5,
    driftRadius: 100,
    fadeDuration: 12,
    stagger: 4,
  },
  {
    // Cycle 3 — fast
    dissolveStart: 120,
    dissolveDuration: 20,
    regenerateStart: 140,
    regenerateDuration: 20,
    patternFrom: 2,
    patternTo: 3,
    particlesPerLine: 4,
    driftRadius: 80,
    fadeDuration: 10,
    stagger: 2,
  },
] as const;

// Terminal heartbeat
export const TERMINAL = {
  x: 960,
  y: 980,
  width: 800,
  command: 'pdd generate',
  successMark: '\u2713',
  fontSize: 11,
  color: '#64748B',
  opacity: 0.5,
  // Frames at which terminal shows checkmark
  checkFrames: [40, 95, 140] as number[],
} as const;

export const TOTAL_FRAMES = 240;
