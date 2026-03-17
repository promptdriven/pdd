// Closing07TheBeat — "The Beat" Dramatic Silence constants

export const DURATION_FRAMES = 120;
export const FPS = 30;

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;

// Background colors
export const BG_START = '#080E1A';
export const BG_END = '#060A12';

// Triangle geometry — centered at (960, 520)
export const TRIANGLE_CENTER: [number, number] = [960, 520];
export const TRIANGLE_VERTICES: [number, number][] = [
  [960, 280],   // top (PROMPT)
  [710, 713],   // bottom-left (TESTS)
  [1210, 713],  // bottom-right (GROUNDING)
];

// Ghost triangle styling
export const EDGE_COLOR = '#475569';
export const EDGE_OPACITY_START = 0.8;
export const EDGE_OPACITY_END = 0.08;
export const EDGE_WIDTH_START = 3;
export const EDGE_WIDTH_END = 1;

// Node colors and sizing
export const NODE_COLORS = {
  PROMPT: '#4A90D9',
  TESTS: '#D9944A',
  GROUNDING: '#5AAA6E',
} as const;

export const NODE_RADIUS_START = 24;
export const NODE_RADIUS_END = 12;
export const NODE_OPACITY_START = 1.0;
export const NODE_OPACITY_END = 0.06;

// Single particle
export const PARTICLE_START: [number, number] = [960, 650];
export const PARTICLE_END: [number, number] = [960, 350];
export const PARTICLE_SIZE = 2;
export const PARTICLE_COLOR = '#E2E8F0';
export const PARTICLE_BASE_OPACITY = 0.12;
export const PARTICLE_GLINT_Y = 520;
export const PARTICLE_GLINT_PEAK_OPACITY = 0.25;
export const PARTICLE_GLINT_DURATION = 6;
export const PARTICLE_DRIFT_DURATION = 90;

// Vignette
export const VIGNETTE_EDGE_OPACITY = 0.5;

// Animation timing (frames)
export const GHOST_FADE_DURATION = 30;
export const NODE_SHRINK_DURATION = 25;
export const GLOW_DISSOLVE_DURATION = 20;
export const BG_DARKEN_DURATION = 30;
export const VIGNETTE_FADE_START = 20;
export const VIGNETTE_FADE_DURATION = 20;
export const PARTICLE_START_FRAME = 30;
