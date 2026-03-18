// Closing01SockCallbackSplit constants

export const CANVAS = {
  WIDTH: 1920,
  HEIGHT: 1080,
  BACKGROUND: '#000000',
  DURATION_FRAMES: 240,
  FPS: 30,
} as const;

export const SPLIT = {
  X: 960,
  DIVIDER_WIDTH: 2,
  DIVIDER_COLOR: '#334155',
  DIVIDER_OPACITY: 0.15,
  LEFT_WIDTH: 958,
  RIGHT_X: 962,
  RIGHT_WIDTH: 958,
} as const;

export const COLORS = {
  AMBER: '#D9944A',
  AMBER_GRADE: '#D4A043',
  BLUE: '#4A90D9',
  BLUE_GRADE: '#4A90D9',
  SUBTITLE: '#94A3B8',
  LEFT_VIGNETTE: '#0A0500',
  RIGHT_VIGNETTE: '#000510',
} as const;

export const TIMING = {
  // Phase 1: Split line + headers (0-15)
  SPLIT_DRAW_START: 0,
  SPLIT_DRAW_DURATION: 12,
  HEADER_FADE_START: 3,
  HEADER_FADE_DURATION: 12,

  // Phase 2-4: Veo clips play (15-160)
  VEO_START: 0,

  // Terminal snippet typewriter
  TERMINAL_START: 120,
  TERMINAL_DURATION: 40,

  // Phase 5: Cost labels (160-200)
  COST_LABEL_START: 160,
  COST_LABEL_DURATION: 18,
  SUB_LABEL_DELAY: 6,
  SUB_LABEL_DURATION: 12,
} as const;
