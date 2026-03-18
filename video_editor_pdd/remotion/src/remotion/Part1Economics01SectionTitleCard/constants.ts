// Part1Economics01SectionTitleCard - constants

export const CANVAS = {
  WIDTH: 1920,
  HEIGHT: 1080,
  FPS: 30,
  DURATION_FRAMES: 120,
} as const;

export const COLORS = {
  background: '#0D1117',
  amber: '#D9944A',
  slate: '#94A3B8',
} as const;

export const TIMING = {
  // Frame 0-15: Background settles
  BG_SETTLE_END: 15,
  // Frame 15-35: Part label fade-in + slide
  PART_LABEL_START: 15,
  PART_LABEL_DURATION: 15,
  // Frame 35-60: Title fade-in + slide
  TITLE_START: 35,
  TITLE_DURATION: 20,
  // Frame 60-70: Horizontal rule draws
  RULE_START: 60,
  RULE_DURATION: 10,
  // Frame 70-90: Subtitle fade-in
  SUBTITLE_START: 70,
  SUBTITLE_DURATION: 15,
  // Frame 90-120: Hold
} as const;

export const LAYOUT = {
  partLabelY: 420,
  titleY: 500,
  ruleY: 555,
  subtitleY: 585,
  ruleTotalWidth: 120,
  ruleThickness: 2,
  centerX: 960,
} as const;
