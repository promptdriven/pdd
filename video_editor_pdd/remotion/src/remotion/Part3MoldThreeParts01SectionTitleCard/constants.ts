// constants.ts — Part3MoldThreeParts01SectionTitleCard

export const CANVAS = {
  WIDTH: 1920,
  HEIGHT: 1080,
  BG_COLOR: '#0A0F1A',
} as const;

export const GRID = {
  SPACING: 60,
  COLOR: '#1E293B',
  OPACITY: 0.05,
} as const;

export const COLORS = {
  TITLE: '#E2E8F0',
  SECTION_LABEL: '#64748B',
  RULE: '#334155',
  WALL: '#D9944A',
  NOZZLE: '#4A90D9',
  MATERIAL: '#5AAA6E',
} as const;

export const GHOST_ELEMENTS = [
  {
    shape: 'wall' as const,
    label: 'WALLS',
    color: COLORS.WALL,
    x: 560,
    y: 480,
  },
  {
    shape: 'nozzle' as const,
    label: 'NOZZLE',
    color: COLORS.NOZZLE,
    x: 960,
    y: 430,
  },
  {
    shape: 'material' as const,
    label: 'MATERIAL',
    color: COLORS.MATERIAL,
    x: 1360,
    y: 480,
  },
] as const;

export const TIMING = {
  BG_FADE_END: 15,
  PART3_FADE_START: 15,
  GHOST_DRAW_START: 15,
  GHOST_DRAW_DURATION: 60,
  TITLE1_START: 40,
  TITLE1_TEXT: 'THE MOLD HAS',
  TITLE1_CHAR_DELAY: 3,
  RULE_START: 60,
  RULE_DRAW_DURATION: 10,
  TITLE2_START: 70,
  TITLE2_FADE_DURATION: 20,
  TITLE2_SLIDE_DISTANCE: 10,
  PULSE_CYCLE: 30,
  TOTAL_FRAMES: 120,
} as const;
