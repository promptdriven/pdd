// Part 4 Section Title Card — The Precision Tradeoff
// Component-level constants

export const CANVAS = {
  WIDTH: 1920,
  HEIGHT: 1080,
  BACKGROUND: '#0A0F1A',
} as const;

export const GRID = {
  SPACING: 60,
  COLOR: '#1E293B',
  OPACITY: 0.05,
} as const;

export const COLORS = {
  TITLE_TEXT: '#E2E8F0',
  SECTION_LABEL: '#64748B',
  RULE: '#334155',
  DOT_GRID: '#94A3B8',
  MOLD_OUTLINE: '#D9944A',
} as const;

export const TITLE = {
  SECTION_LABEL: 'PART 4',
  LINE1: 'THE PRECISION',
  LINE2: 'TRADEOFF',
  FONT_SIZE: 72,
  FONT_WEIGHT: 700,
  LABEL_SIZE: 14,
  LABEL_WEIGHT: 600,
  LABEL_LETTER_SPACING: 4,
} as const;

export const POSITIONS = {
  SECTION_LABEL_Y: 400,
  TITLE_LINE1_Y: 460,
  RULE_Y: 505,
  TITLE_LINE2_Y: 545,
  TITLE_LINE2_OFFSET_X: 15,
  DOT_GRID: { x: 560, y: 480 },
  MOLD_OUTLINE: { x: 1360, y: 480 },
  CENTER_X: 960,
} as const;

export const DOT_MATRIX = {
  ROWS: 8,
  COLS: 8,
  DOT_SIZE: 4,
  SPACING: 12,
  OPACITY: 0.03,
  GLOW_BLUR: 8,
  GLOW_OPACITY: 0.02,
  LABEL: 'EVERY POINT',
} as const;

export const MOLD = {
  OPACITY: 0.04,
  STROKE_WIDTH: 3,
  GLOW_BLUR: 8,
  GLOW_OPACITY: 0.02,
  LABEL: 'WALLS ONLY',
  WIDTH: 80,
  HEIGHT: 60,
} as const;

export const RULE = {
  WIDTH: 200,
  HEIGHT: 2,
  OPACITY: 0.5,
} as const;

// Animation timing (frames)
export const TIMING = {
  BG_FADE_START: 0,
  BG_FADE_END: 15,
  GHOST_START: 15,
  GHOST_DOTS_STAGGER: 1,       // frames per dot
  GHOST_WALL_DURATION: 40,
  SECTION_LABEL_START: 15,
  SECTION_LABEL_FADE: 20,
  TITLE_LINE1_START: 40,
  TITLE_LINE1_CHAR_DELAY: 3,
  RULE_START: 60,
  RULE_DRAW_DURATION: 10,
  TITLE_LINE2_START: 70,
  TITLE_LINE2_FADE: 20,
  TITLE_LINE2_SLIDE: 10,       // px slide-up distance
  HOLD_START: 90,
  TOTAL_FRAMES: 120,
  PULSE_CYCLE: 30,
} as const;

export const GHOST_LABEL = {
  FONT_SIZE: 8,
  OPACITY: 0.03,
} as const;
