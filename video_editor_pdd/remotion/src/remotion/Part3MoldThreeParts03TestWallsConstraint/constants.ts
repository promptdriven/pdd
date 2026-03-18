// ── Colors ──
export const BG_COLOR = '#0A0F1A';
export const WALL_COLOR = '#D9944A';
export const WALL_COLOR_DIM = 'rgba(217, 148, 74, 0.4)';
export const WALL_FLASH_COLOR = 'rgba(217, 148, 74, 1.0)';
export const WALL_RIPPLE_COLOR = 'rgba(217, 148, 74, 0.2)';
export const CAVITY_COLOR = 'rgba(30, 41, 59, 0.15)';
export const LIQUID_COLOR = '#4A90D9';
export const LIQUID_GLOW = 'rgba(74, 144, 217, 0.2)';
export const TERMINAL_BG = 'rgba(15, 23, 42, 0.85)';
export const TERMINAL_BORDER = '#334155';
export const TERMINAL_TEXT = '#94A3B8';
export const TERMINAL_GREEN = '#5AAA6E';
export const LABEL_COLOR_DIM = 'rgba(217, 148, 74, 0.3)';
export const LABEL_COLOR_BRIGHT = 'rgba(217, 148, 74, 1.0)';

// ── Dimensions ──
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 360;

// ── Mold geometry ──
export const MOLD_CENTER_X = 960;
export const MOLD_CENTER_Y = 500;
export const MOLD_WIDTH = 600;
export const MOLD_HEIGHT = 700;
export const WALL_STROKE = 4;

// Mold cavity bounds (inner area for liquid)
export const CAVITY_LEFT = MOLD_CENTER_X - MOLD_WIDTH / 2 + 40;
export const CAVITY_RIGHT = MOLD_CENTER_X + MOLD_WIDTH / 2 - 40;
export const CAVITY_TOP = MOLD_CENTER_Y - MOLD_HEIGHT / 2 + 60;
export const CAVITY_BOTTOM = MOLD_CENTER_Y + MOLD_HEIGHT / 2 - 40;

// Nozzle entry point
export const NOZZLE_X = MOLD_CENTER_X;
export const NOZZLE_Y = MOLD_CENTER_Y - MOLD_HEIGHT / 2 - 20;

// ── Wall segments with labels ──
export interface WallSegment {
	id: string;
	label: string;
	x1: number;
	y1: number;
	x2: number;
	y2: number;
	normalX: number;
	normalY: number;
}

export const WALL_SEGMENTS: WallSegment[] = [
	// Left wall
	{
		id: 'left-top',
		label: 'null → None',
		x1: CAVITY_LEFT,
		y1: CAVITY_TOP,
		x2: CAVITY_LEFT,
		y2: CAVITY_TOP + 200,
		normalX: 1,
		normalY: 0,
	},
	{
		id: 'left-mid',
		label: 'int → str',
		x1: CAVITY_LEFT,
		y1: CAVITY_TOP + 200,
		x2: CAVITY_LEFT + 60,
		y2: CAVITY_TOP + 350,
		normalX: 0.8,
		normalY: 0.2,
	},
	{
		id: 'left-bottom',
		label: 'empty list',
		x1: CAVITY_LEFT + 60,
		y1: CAVITY_TOP + 350,
		x2: CAVITY_LEFT + 60,
		y2: CAVITY_BOTTOM,
		normalX: 1,
		normalY: 0,
	},
	// Right wall
	{
		id: 'right-top',
		label: 'max_length',
		x1: CAVITY_RIGHT,
		y1: CAVITY_TOP,
		x2: CAVITY_RIGHT,
		y2: CAVITY_TOP + 180,
		normalX: -1,
		normalY: 0,
	},
	{
		id: 'right-mid',
		label: 'utf-8 edge',
		x1: CAVITY_RIGHT,
		y1: CAVITY_TOP + 180,
		x2: CAVITY_RIGHT - 50,
		y2: CAVITY_TOP + 380,
		normalX: -0.8,
		normalY: 0.2,
	},
	{
		id: 'right-bottom',
		label: 'KeyError',
		x1: CAVITY_RIGHT - 50,
		y1: CAVITY_TOP + 380,
		x2: CAVITY_RIGHT - 50,
		y2: CAVITY_BOTTOM,
		normalX: -1,
		normalY: 0,
	},
	// Bottom wall
	{
		id: 'bottom',
		label: 'return type',
		x1: CAVITY_LEFT + 60,
		y1: CAVITY_BOTTOM,
		x2: CAVITY_RIGHT - 50,
		y2: CAVITY_BOTTOM,
		normalX: 0,
		normalY: -1,
	},
	// Top wall (with nozzle gap)
	{
		id: 'top-left',
		label: 'import check',
		x1: CAVITY_LEFT,
		y1: CAVITY_TOP,
		x2: MOLD_CENTER_X - 30,
		y2: CAVITY_TOP,
		normalX: 0,
		normalY: 1,
	},
	{
		id: 'top-right',
		label: 'type hints',
		x1: MOLD_CENTER_X + 30,
		y1: CAVITY_TOP,
		x2: CAVITY_RIGHT,
		y2: CAVITY_TOP,
		normalX: 0,
		normalY: 1,
	},
];

// ── Collision timeline (which wall, at which frame) ──
export interface CollisionEvent {
	wallId: string;
	frame: number;
	intensity: number;
}

export const COLLISION_EVENTS: CollisionEvent[] = [
	{ wallId: 'right-top', frame: 50, intensity: 0.8 },
	{ wallId: 'left-top', frame: 70, intensity: 0.9 },
	{ wallId: 'left-top', frame: 110, intensity: 1.0 }, // Focus collision: "null → None"
	{ wallId: 'right-mid', frame: 170, intensity: 0.7 },
	{ wallId: 'left-mid', frame: 200, intensity: 0.6 },
	{ wallId: 'left-bottom', frame: 230, intensity: 0.5 },
	{ wallId: 'right-bottom', frame: 250, intensity: 0.5 },
	{ wallId: 'bottom', frame: 270, intensity: 0.6 },
];

// ── Terminal commands ──
export const TERMINAL_COMMANDS = [
	{ text: '$ pdd generate user_parser', color: TERMINAL_TEXT, delay: 0 },
	{ text: '  Generating...', color: TERMINAL_TEXT, delay: 30 },
	{ text: '  ✓ Parser skeleton created', color: TERMINAL_GREEN, delay: 60 },
	{ text: '  ✓ Running test suite...', color: TERMINAL_GREEN, delay: 80 },
	{ text: '  ✓ All 12 tests passing', color: TERMINAL_GREEN, delay: 110 },
];

// ── Font ──
export const MONO_FONT = 'JetBrains Mono, Menlo, monospace';
