// constants.ts — WhereToStart07NoBigBangCallout

export const CANVAS = {
  WIDTH: 1920,
  HEIGHT: 1080,
  BG: '#0A0F1A',
} as const;

export const COLORS = {
  TEXT_PRIMARY: '#E2E8F0',
  NEUTRAL_GRAY: '#64748B',
  GLOW_BLUE: '#4A90D9',
  RULE_COLOR: '#334155',
  GHOST_BLUE: '#4A90D9',
} as const;

export const TIMING = {
  // Ghost background settles
  GHOST_START: 0,
  GHOST_END: 20,

  // Line 1: "One module at a time."
  LINE1_START: 20,
  LINE1_DURATION: 20,

  // Line 2: "No big bang. No rewrite."
  LINE2_START: 50,
  LINE2_DURATION: 18,

  // Horizontal rule draws from center
  RULE_START: 75,
  RULE_DURATION: 12,

  // Line 3 first part
  LINE3_START: 90,
  LINE3_DURATION: 25,

  // Line 3 second part ("from code to specification.")
  LINE3B_START: 100, // 90 + 10
  LINE3B_DURATION: 20,

  // Final glow pulse on "specification"
  PULSE_START: 130,
  PULSE_DURATION: 20,

  TOTAL: 150,
} as const;

export const TYPOGRAPHY = {
  FONT_FAMILY: 'Inter, system-ui, -apple-system, sans-serif',
} as const;
