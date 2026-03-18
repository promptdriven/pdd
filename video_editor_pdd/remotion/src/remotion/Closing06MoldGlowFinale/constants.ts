// ─── Canvas ────────────────────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 240;

// ─── Background ────────────────────────────────────────────────────
export const BG_FROM = '#0A1225';
export const BG_TO = '#080E1A';
export const BG_DARKEN_DURATION = 60; // frames

// ─── Triangle geometry ─────────────────────────────────────────────
export const TRIANGLE_CENTER: [number, number] = [960, 520];
export const TRIANGLE_VERTICES: [number, number][] = [
  [960, 280],   // top — PROMPT
  [710, 713],   // bottom-left — TESTS
  [1210, 713],  // bottom-right — GROUNDING
];

// ─── Edge styling ──────────────────────────────────────────────────
export const EDGE_COLOR_FROM = '#94A3B8';
export const EDGE_COLOR_TO = '#E2E8F0';
export const EDGE_WIDTH_FROM = 2;
export const EDGE_WIDTH_TO = 3;
export const EDGE_OPACITY_FROM = 0.6;
export const EDGE_OPACITY_TO = 0.8;

export const GLOW_LAYERS = [
  { blur: 8, color: '#E2E8F0', opacity: 0.08, delay: 0 },
  { blur: 20, color: '#E2E8F0', opacity: 0.03, delay: 10 },
  { blur: 40, color: '#475569', opacity: 0.02, delay: 20 },
] as const;

// ─── Nodes ─────────────────────────────────────────────────────────
export const NODES = [
  {
    label: 'PROMPT',
    center: [960, 280] as [number, number],
    fillFrom: '#4A90D9',
    fillTo: '#6AB0F0',
    glowColor: '#4A90D9',
  },
  {
    label: 'TESTS',
    center: [710, 713] as [number, number],
    fillFrom: '#D9944A',
    fillTo: '#F0B86A',
    glowColor: '#D9944A',
  },
  {
    label: 'GROUNDING',
    center: [1210, 713] as [number, number],
    fillFrom: '#5AAA6E',
    fillTo: '#7CC98E',
    glowColor: '#5AAA6E',
  },
] as const;

export const NODE_RADIUS_FROM = 20;
export const NODE_RADIUS_TO = 24;
export const NODE_GLOW_RADIUS = 30;
export const NODE_GLOW_OPACITY = 0.12;
export const NODE_GROW_DURATION = 50; // frames
export const NODE_PULSE_PERIOD = 45; // frames
export const NODE_ANIM_START = 30; // frame offset

// ─── Code lines ────────────────────────────────────────────────────
export const CODE_OPACITY_FROM = 0.15;
export const CODE_OPACITY_TO = 0.04;
export const CODE_DIM_DURATION = 60; // frames
export const CODE_DIM_START = 30; // frame offset
export const CODE_COLOR = '#94A3B8';

export const CODE_LINES = [
  'const result = await generateOutput(spec);',
  'if (result.valid) {',
  '  deploy(result.artifact);',
  '} else {',
  '  refine(prompt, result.errors);',
  '}',
];

// ─── Thesis text ───────────────────────────────────────────────────
export const THESIS_TEXT = 'The code is just plastic.';
export const THESIS_FONT = 'Inter';
export const THESIS_SIZE = 24;
export const THESIS_COLOR = '#E2E8F0';
export const THESIS_OPACITY = 0.6;
export const THESIS_Y = 840;
export const THESIS_START = 130; // frame offset
export const THESIS_FADE_DURATION = 20;

export const HR_WIDTH = 120;
export const HR_Y = 825;
export const HR_COLOR = '#475569';
export const HR_OPACITY = 0.1;
export const HR_DRAW_DURATION = 12;

// ─── Particle field ────────────────────────────────────────────────
export const PARTICLE_COUNT = 35;
export const PARTICLE_COLORS = ['#4A90D9', '#D9944A', '#5AAA6E'];
export const PARTICLE_SPEED_RANGE: [number, number] = [0.3, 0.8];
export const PARTICLE_SIZE_RANGE: [number, number] = [1, 3];
export const PARTICLE_OPACITY_RANGE: [number, number] = [0.06, 0.1];
export const PARTICLE_SPAWN_Y_RANGE: [number, number] = [700, 1080];
