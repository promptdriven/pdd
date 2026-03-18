// Closing07TheBeat - "The Beat" Dramatic Silence constants

export const DURATION_FRAMES = 120;
export const FPS = 30;
export const WIDTH = 1920;
export const HEIGHT = 1080;

// Background colors
export const BG_START = '#080E1A';
export const BG_END = '#060A12';

// Triangle geometry — centered at (960, 520)
export const TRIANGLE_CENTER: [number, number] = [960, 520];
export const TRIANGLE_VERTICES: [number, number][] = [
  [960, 280],   // PROMPT (top)
  [710, 713],   // TESTS (bottom-left)
  [1210, 713],  // GROUNDING (bottom-right)
];

// Node colors
export const NODE_PROMPT_COLOR = '#4A90D9';
export const NODE_TESTS_COLOR = '#D9944A';
export const NODE_GROUNDING_COLOR = '#5AAA6E';

// Ghost state targets
export const GHOST_EDGE_COLOR = '#475569';
export const GHOST_EDGE_OPACITY = 0.08;
export const GHOST_EDGE_WIDTH = 1;
export const GHOST_NODE_RADIUS = 12;
export const GHOST_NODE_OPACITY = 0.06;

// Initial (luminous) state
export const LUMINOUS_EDGE_OPACITY = 0.8;
export const LUMINOUS_EDGE_WIDTH = 3;
export const LUMINOUS_NODE_RADIUS = 24;
export const LUMINOUS_NODE_OPACITY = 1.0;

// Single particle
export const PARTICLE_START: [number, number] = [960, 650];
export const PARTICLE_END: [number, number] = [960, 350];
export const PARTICLE_SIZE = 2;
export const PARTICLE_COLOR = '#E2E8F0';
export const PARTICLE_BASE_OPACITY = 0.12;
export const PARTICLE_GLINT_Y = 520;
export const PARTICLE_GLINT_PEAK_OPACITY = 0.25;
export const PARTICLE_GLINT_DURATION = 6;

// Vignette
export const VIGNETTE_EDGE_OPACITY = 0.5;
export const VIGNETTE_EDGE_COLOR = '#000000';
