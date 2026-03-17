// Closing06MoldGlowFinale — constants

export const DURATION_FRAMES = 240;
export const FPS = 30;

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;

// Backgrounds
export const BG_START = '#0A1225';
export const BG_END = '#080E1A';

// Triangle geometry — centered at (960, 520)
export const TRIANGLE_CENTER = { x: 960, y: 520 };
export const TRIANGLE_VERTICES: [number, number][] = [
	[960, 280], // top — PROMPT
	[710, 713], // bottom-left — TESTS
	[1210, 713], // bottom-right — GROUNDING
];

// Edge styling
export const EDGE_WIDTH_START = 2;
export const EDGE_WIDTH_END = 3;
export const EDGE_COLOR_START = '#94A3B8';
export const EDGE_COLOR_END = '#E2E8F0';
export const EDGE_OPACITY_START = 0.6;
export const EDGE_OPACITY_END = 0.8;

// Glow layers
export const GLOW_LAYERS = [
	{ blur: 8, color: '#E2E8F0', opacity: 0.08, delay: 0 },
	{ blur: 20, color: '#E2E8F0', opacity: 0.03, delay: 10 },
	{ blur: 40, color: '#475569', opacity: 0.02, delay: 20 },
];

// Nodes
export const NODE_RADIUS_START = 20;
export const NODE_RADIUS_END = 24;
export const NODE_GROW_DURATION = 50;
export const NODE_PULSE_PERIOD = 45;

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
];

export const NODE_GLOW_RADIUS = 30;
export const NODE_GLOW_OPACITY = 0.12;

// Code lines
export const CODE_OPACITY_START = 0.15;
export const CODE_OPACITY_END = 0.04;
export const CODE_COLOR = '#94A3B8';
export const CODE_DIM_DURATION = 60;

// Code line patterns (widths as percentages of max width)
export const CODE_LINE_WIDTHS = [
	0.6, 0.85, 0.45, 0.7, 0.55, 0.9, 0.4, 0.75, 0.65, 0.5,
];

// Thesis text
export const THESIS_TEXT = 'The code is just plastic.';
export const THESIS_FONT_SIZE = 24;
export const THESIS_COLOR = '#E2E8F0';
export const THESIS_OPACITY = 0.6;
export const THESIS_Y = 840;
export const THESIS_APPEAR_FRAME = 130;

// Horizontal rule
export const HR_WIDTH = 120;
export const HR_Y = 825;
export const HR_COLOR = '#475569';
export const HR_OPACITY = 0.1;

// Particles
export const PARTICLE_COUNT = 35;
export const PARTICLE_COLORS = ['#4A90D9', '#D9944A', '#5AAA6E'];
export const PARTICLE_SPEED_MIN = 0.3;
export const PARTICLE_SPEED_MAX = 0.8;
export const PARTICLE_SIZE_MIN = 1;
export const PARTICLE_SIZE_MAX = 3;
export const PARTICLE_SPAWN_Y_MIN = 700;
export const PARTICLE_SPAWN_Y_MAX = 1080;
export const PARTICLE_OPACITY_MIN = 0.06;
export const PARTICLE_OPACITY_MAX = 0.1;
