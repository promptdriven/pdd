// constants.ts — Closing 08: The Mold Is What Matters

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = '#060A12';

// Triangle geometry — centered at (960, 520)
export const TRIANGLE_CENTER: [number, number] = [960, 520];
export const TRIANGLE_VERTICES: [number, number][] = [
  [960, 280],   // top (PROMPT)
  [710, 713],   // bottom-left (TESTS)
  [1210, 713],  // bottom-right (GROUNDING)
];

// Edge styling
export const EDGE_COLOR = '#E2E8F0';
export const EDGE_WIDTH = 2.5;
export const EDGE_OPACITY_START = 0.08;
export const EDGE_OPACITY_END = 0.7;
export const GLOW_1_BLUR = 10;
export const GLOW_1_OPACITY = 0.1;
export const GLOW_2_BLUR = 25;
export const GLOW_2_OPACITY = 0.04;

// Node definitions
export const NODES = [
  {
    label: 'PROMPT',
    center: [960, 280] as [number, number],
    fillColor: '#6AB0F0',
    glowColor: '#4A90D9',
    glowOpacity: 0.15,
  },
  {
    label: 'TESTS',
    center: [710, 713] as [number, number],
    fillColor: '#F0B86A',
    glowColor: '#D9944A',
    glowOpacity: 0.15,
  },
  {
    label: 'GROUNDING',
    center: [1210, 713] as [number, number],
    fillColor: '#7CC98E',
    glowColor: '#5AAA6E',
    glowOpacity: 0.15,
  },
] as const;

// Node sizing
export const NODE_RADIUS_START = 12;
export const NODE_RADIUS_END = 22;
export const NODE_GLOW_RADIUS = 35;
export const PULSE_MIN = 22;
export const PULSE_MAX = 24;
export const PULSE_PERIOD = 90; // frames

// Animation timing (frames)
export const EDGE_REIGNITE_DURATION = 15;
export const NODE_GROW_DURATION = 18;
export const GLOW_APPEAR_DURATION = 20;
export const THESIS_FADE_START = 80;
export const THESIS_FADE_DURATION = 20;

// Thesis text
export const THESIS_TEXT = 'The mold is what matters.';
export const THESIS_FONT_SIZE = 28;
export const THESIS_FONT_WEIGHT = 600;
export const THESIS_COLOR = '#E2E8F0';
export const THESIS_OPACITY = 0.75;
export const THESIS_LETTER_SPACING = 0.5;
export const THESIS_Y = 860;

// Total duration
export const TOTAL_FRAMES = 180;
