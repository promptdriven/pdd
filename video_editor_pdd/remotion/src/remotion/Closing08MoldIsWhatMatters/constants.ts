// === Colors ===
export const BG_COLOR = '#060A12';
export const EDGE_COLOR = '#E2E8F0';
export const TEXT_COLOR = '#E2E8F0';

// Node colors
export const PROMPT_FILL = '#6AB0F0';
export const PROMPT_GLOW = '#4A90D9';
export const TESTS_FILL = '#F0B86A';
export const TESTS_GLOW = '#D9944A';
export const GROUNDING_FILL = '#7CC98E';
export const GROUNDING_GLOW = '#5AAA6E';

export const NODE_GLOW_OPACITY = 0.15;

// === Dimensions ===
export const WIDTH = 1920;
export const HEIGHT = 1080;

// Triangle geometry — centered at (960, 520)
export const TRIANGLE_VERTICES: [number, number][] = [
  [960, 280],   // top (PROMPT)
  [710, 713],   // bottom-left (TESTS)
  [1210, 713],  // bottom-right (GROUNDING)
];

export const EDGE_WIDTH = 2.5;
export const EDGE_OPACITY_START = 0.08;
export const EDGE_OPACITY_END = 0.7;

// Glow layers
export const EDGE_GLOW_1_BLUR = 10;
export const EDGE_GLOW_1_OPACITY = 0.1;
export const EDGE_GLOW_2_BLUR = 25;
export const EDGE_GLOW_2_OPACITY = 0.04;

// Node sizing
export const NODE_RADIUS_START = 12;
export const NODE_RADIUS_END = 22;
export const NODE_GLOW_RADIUS = 35;
export const NODE_PULSE_MIN = 22;
export const NODE_PULSE_MAX = 24;
export const NODE_PULSE_PERIOD = 90;

// === Timing (frames) ===
export const REIGNITE_EDGE_DURATION = 15;
export const NODE_GROW_DURATION = 18;
export const GLOW_APPEAR_DURATION = 20;
export const THESIS_TEXT_START = 80;
export const THESIS_TEXT_FADE_DURATION = 20;
export const TOTAL_DURATION = 180;

// === Typography ===
export const THESIS_TEXT = 'The mold is what matters.';
export const THESIS_FONT_SIZE = 28;
export const THESIS_FONT_WEIGHT = 600;
export const THESIS_TEXT_OPACITY = 0.75;
export const THESIS_LETTER_SPACING = 0.5;
export const THESIS_Y = 860;
