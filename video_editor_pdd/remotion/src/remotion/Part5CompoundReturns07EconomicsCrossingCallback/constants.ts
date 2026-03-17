// constants.ts — Component-level constants, colors, dimensions, and data

export const CANVAS = {
  WIDTH: 1920,
  HEIGHT: 1080,
  BG: '#0F172A',
} as const;

export const COLORS = {
  bg: '#0F172A',
  gridLine: '#1E293B',
  amber: '#D9944A',
  blue: '#4A90D9',
  text: '#E2E8F0',
  axisLabel: '#64748B',
  greenZone: '#22C55E',
  redZone: '#EF4444',
  needle: '#94A3B8',
  strikethrough: '#EF4444',
} as const;

export const OPACITIES = {
  gridLine: 0.06,
  axisLabel: 0.5,
  lineLabel: 0.7,
  crossingGlow: 0.2,
  crossingCircle: 0.9,
  greenZone: 0.08,
  redZone: 0.08,
  needle: 0.4,
  strikethrough: 0.5,
} as const;

// Chart area padding
export const CHART = {
  left: 140,
  right: 100,
  top: 80,
  bottom: 80,
  width: 1920 - 140 - 100, // 1680
  height: 1080 - 80 - 80,  // 920
} as const;

// Animation frame ranges
export const FRAMES = {
  // Phase 1: Chart fade-in
  fadeInStart: 0,
  fadeInEnd: 30,
  // Phase 2: Crossing pulse starts
  pulseStart: 30,
  // Phase 3: Morph sequence
  morphStart: 60,
  morphEnd: 150,
  // Phase 4: Post-crossing relabel
  relabelStart: 150,
  relabelEnd: 210,
  // Phase 5: Darning needle
  needleStart: 210,
  needleScaleDuration: 15,
  strikethroughDelay: 10,
  strikethroughDuration: 10,
  // Phase 6: Hold
  holdStart: 240,
  total: 300,
} as const;

// Y-axis range
export const Y_RANGE = { min: 0, max: 30 } as const;

// Initial (sock economics) data
export const INITIAL_DATA = {
  xLabels: ['1950', '1960', '1970', '1980', '1990', '2000', '2010', '2020'],
  xRange: [1950, 2020] as [number, number],
  crossingYear: 1962,
  crossingLabel: 'The Threshold',
  postCrossingLabel: 'Darning irrational',
  line1Label: 'Labor cost (per hour)',
  line2Label: 'Sock cost',
  // Labor cost rising from $2 to $25
  laborData: [
    { x: 1950, y: 2 },
    { x: 1960, y: 4 },
    { x: 1962, y: 4.5 },
    { x: 1970, y: 7 },
    { x: 1980, y: 11 },
    { x: 1990, y: 15 },
    { x: 2000, y: 19 },
    { x: 2010, y: 22 },
    { x: 2020, y: 25 },
  ],
  // Sock cost falling from $8 to $0.50
  sockData: [
    { x: 1950, y: 8 },
    { x: 1960, y: 5 },
    { x: 1962, y: 4.5 },
    { x: 1970, y: 3 },
    { x: 1980, y: 2 },
    { x: 1990, y: 1.5 },
    { x: 2000, y: 1 },
    { x: 2010, y: 0.7 },
    { x: 2020, y: 0.5 },
  ],
} as const;

// Final (code economics) data
export const FINAL_DATA = {
  xLabels: ['2020', '2022', '2024', '2026', '2028', '2030'],
  xRange: [2020, 2030] as [number, number],
  crossingYear: 2024,
  crossingLabel: 'Now',
  postCrossingLabel: 'Patching irrational',
  line1Label: 'Patching cost (per fix)',
  line2Label: 'Generation cost',
  // Patching cost rising
  laborData: [
    { x: 2020, y: 3 },
    { x: 2022, y: 6 },
    { x: 2024, y: 10 },
    { x: 2026, y: 16 },
    { x: 2028, y: 21 },
    { x: 2030, y: 25 },
  ],
  // Generation cost falling
  sockData: [
    { x: 2020, y: 18 },
    { x: 2022, y: 13 },
    { x: 2024, y: 10 },
    { x: 2026, y: 6 },
    { x: 2028, y: 3 },
    { x: 2030, y: 1 },
  ],
} as const;

// Needle icon position
export const NEEDLE_POS = { x: 1400, y: 600 } as const;
