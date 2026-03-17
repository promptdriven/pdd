// Component-level constants for WhereToStart07NoBigBangCallout

export const CANVAS = {
  WIDTH: 1920,
  HEIGHT: 1080,
  BACKGROUND: '#0A0F1A',
} as const;

export const COLORS = {
  TEXT_PRIMARY: '#E2E8F0',
  TEXT_GRAY: '#64748B',
  TEXT_BLUE: '#4A90D9',
  RULE: '#334155',
  GHOST_BLUE: '#4A90D9',
} as const;

export const TIMING = {
  // Ghost background settle
  GHOST_SETTLE_START: 0,
  GHOST_SETTLE_END: 20,
  // Line 1: "One module at a time."
  LINE1_START: 20,
  LINE1_DURATION: 20,
  LINE1_SLIDE: 8,
  // Line 2: "No big bang. No rewrite."
  LINE2_START: 50,
  LINE2_DURATION: 18,
  LINE2_SLIDE: 6,
  // Horizontal rule
  RULE_START: 75,
  RULE_DURATION: 12,
  // Line 3: main text
  LINE3_START: 90,
  LINE3_DURATION: 25,
  // Line 3: "from code to specification."
  LINE3B_OFFSET: 10,
  LINE3B_DURATION: 20,
  // Final glow pulse
  PULSE_START: 130,
  PULSE_DURATION: 20,
  // Total
  TOTAL_FRAMES: 150,
} as const;

export const TYPOGRAPHY = {
  FONT_FAMILY: 'Inter, system-ui, -apple-system, sans-serif',
  LINE1: { size: 28, weight: 600 as const, opacity: 0.8, y: 380 },
  LINE2: { size: 22, weight: 400 as const, opacity: 0.5, y: 430 },
  LINE3A: { size: 18, weight: 400 as const, opacity: 0.4, y: 520 },
  LINE3B: { size: 18, weight: 400 as const, y: 555 },
  CODE_OPACITY: 0.5,
  SPEC_OPACITY: 0.7,
  SPEC_GLOW_OPACITY: 0.15,
  SPEC_GLOW_BLUR: 8,
} as const;

export const RULE = {
  WIDTH: 160,
  HEIGHT: 1.5,
  Y: 475,
  OPACITY: 0.3,
} as const;

// Ghost codebase background nodes for the blurred topology
export const GHOST_NODES = [
  // Neutral gray nodes scattered across the canvas
  { x: 320, y: 280, r: 18, color: '#475569' },
  { x: 480, y: 350, r: 14, color: '#475569' },
  { x: 620, y: 220, r: 20, color: '#475569' },
  { x: 750, y: 400, r: 16, color: '#475569' },
  { x: 900, y: 300, r: 22, color: '#475569' },
  { x: 1050, y: 250, r: 15, color: '#475569' },
  { x: 1200, y: 350, r: 19, color: '#475569' },
  { x: 1350, y: 280, r: 17, color: '#475569' },
  { x: 1500, y: 320, r: 21, color: '#475569' },
  { x: 1600, y: 400, r: 13, color: '#475569' },
  // Blue cluster (converted modules)
  { x: 1100, y: 600, r: 26, color: '#4A90D9' },
  { x: 1180, y: 650, r: 22, color: '#4A90D9' },
  { x: 1050, y: 670, r: 20, color: '#4A90D9' },
  { x: 1150, y: 720, r: 18, color: '#4A90D9' },
  // More neutral
  { x: 400, y: 600, r: 16, color: '#475569' },
  { x: 550, y: 700, r: 14, color: '#475569' },
  { x: 700, y: 650, r: 18, color: '#475569' },
  { x: 850, y: 750, r: 15, color: '#475569' },
] as const;
