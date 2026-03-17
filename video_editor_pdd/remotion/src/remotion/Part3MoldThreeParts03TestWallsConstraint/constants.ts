// ── Colors ──
export const BG_COLOR = '#0A0F1A';
export const WALL_COLOR = '#D9944A';
export const WALL_COLOR_DIM = 'rgba(217, 148, 74, 0.4)';
export const WALL_COLOR_FLASH = 'rgba(217, 148, 74, 1.0)';
export const WALL_RIPPLE_COLOR = 'rgba(217, 148, 74, 0.2)';
export const CAVITY_COLOR = 'rgba(30, 41, 59, 0.15)';
export const LIQUID_COLOR = '#4A90D9';
export const LIQUID_COLOR_HALF = 'rgba(74, 144, 217, 0.5)';
export const LIQUID_GLOW = 'rgba(74, 144, 217, 0.2)';
export const TERMINAL_BG = 'rgba(15, 23, 42, 0.85)';
export const TERMINAL_BORDER = '#334155';
export const TERMINAL_TEXT = '#94A3B8';
export const TERMINAL_GREEN = 'rgba(90, 170, 110, 0.7)';
export const LABEL_DIM = 'rgba(217, 148, 74, 0.3)';

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

// Mold boundary box
export const MOLD_LEFT = MOLD_CENTER_X - MOLD_WIDTH / 2;   // 660
export const MOLD_RIGHT = MOLD_CENTER_X + MOLD_WIDTH / 2;  // 1260
export const MOLD_TOP = MOLD_CENTER_Y - MOLD_HEIGHT / 2;   // 150
export const MOLD_BOTTOM = MOLD_CENTER_Y + MOLD_HEIGHT / 2; // 850

// Nozzle entry
export const NOZZLE_X = MOLD_CENTER_X;
export const NOZZLE_Y = MOLD_TOP;

// ── Wall segments with labels ──
export interface WallSegment {
  id: string;
  label: string;
  x1: number;
  y1: number;
  x2: number;
  y2: number;
  labelX: number;
  labelY: number;
  normalX: number; // inward normal
  normalY: number;
}

export const WALL_SEGMENTS: WallSegment[] = [
  // Left wall
  {
    id: 'left-top',
    label: 'null → None',
    x1: MOLD_LEFT, y1: MOLD_TOP + 50,
    x2: MOLD_LEFT, y2: MOLD_TOP + 250,
    labelX: MOLD_LEFT - 90, labelY: MOLD_TOP + 150,
    normalX: 1, normalY: 0,
  },
  {
    id: 'left-mid',
    label: 'empty → []',
    x1: MOLD_LEFT, y1: MOLD_TOP + 250,
    x2: MOLD_LEFT, y2: MOLD_TOP + 450,
    labelX: MOLD_LEFT - 80, labelY: MOLD_TOP + 350,
    normalX: 1, normalY: 0,
  },
  {
    id: 'left-bottom',
    label: 'type: str',
    x1: MOLD_LEFT, y1: MOLD_TOP + 450,
    x2: MOLD_LEFT, y2: MOLD_BOTTOM,
    labelX: MOLD_LEFT - 75, labelY: MOLD_TOP + 575,
    normalX: 1, normalY: 0,
  },
  // Right wall
  {
    id: 'right-top',
    label: 'max_len: 50',
    x1: MOLD_RIGHT, y1: MOLD_TOP + 50,
    x2: MOLD_RIGHT, y2: MOLD_TOP + 250,
    labelX: MOLD_RIGHT + 15, labelY: MOLD_TOP + 150,
    normalX: -1, normalY: 0,
  },
  {
    id: 'right-mid',
    label: 'email format',
    x1: MOLD_RIGHT, y1: MOLD_TOP + 250,
    x2: MOLD_RIGHT, y2: MOLD_TOP + 450,
    labelX: MOLD_RIGHT + 15, labelY: MOLD_TOP + 350,
    normalX: -1, normalY: 0,
  },
  {
    id: 'right-bottom',
    label: 'no spaces',
    x1: MOLD_RIGHT, y1: MOLD_TOP + 450,
    x2: MOLD_RIGHT, y2: MOLD_BOTTOM,
    labelX: MOLD_RIGHT + 15, labelY: MOLD_TOP + 575,
    normalX: -1, normalY: 0,
  },
  // Bottom wall
  {
    id: 'bottom',
    label: 'return UserModel',
    x1: MOLD_LEFT, y1: MOLD_BOTTOM,
    x2: MOLD_RIGHT, y2: MOLD_BOTTOM,
    labelX: MOLD_CENTER_X - 55, labelY: MOLD_BOTTOM + 25,
    normalX: 0, normalY: -1,
  },
  // Top wall (with nozzle gap)
  {
    id: 'top-left',
    label: 'input: dict',
    x1: MOLD_LEFT, y1: MOLD_TOP + 50,
    x2: MOLD_CENTER_X - 40, y2: MOLD_TOP + 50,
    labelX: MOLD_LEFT + 60, labelY: MOLD_TOP + 35,
    normalX: 0, normalY: 1,
  },
  {
    id: 'top-right',
    label: 'raises ValueError',
    x1: MOLD_CENTER_X + 40, y1: MOLD_TOP + 50,
    x2: MOLD_RIGHT, y2: MOLD_TOP + 50,
    labelX: MOLD_CENTER_X + 80, labelY: MOLD_TOP + 35,
    normalX: 0, normalY: 1,
  },
];

// Nozzle shape
export const NOZZLE_WIDTH = 60;
export const NOZZLE_HEIGHT = 55;

// ── Collision timing (frame when liquid hits each wall) ──
export interface CollisionEvent {
  wallId: string;
  frame: number;
  flashDuration: number;
  rippleDuration: number;
}

export const COLLISION_EVENTS: CollisionEvent[] = [
  { wallId: 'right-top', frame: 45, flashDuration: 6, rippleDuration: 15 },
  { wallId: 'left-top', frame: 65, flashDuration: 6, rippleDuration: 15 },
  { wallId: 'right-mid', frame: 130, flashDuration: 6, rippleDuration: 15 },
  { wallId: 'left-mid', frame: 160, flashDuration: 6, rippleDuration: 15 },
  { wallId: 'right-bottom', frame: 200, flashDuration: 6, rippleDuration: 15 },
  { wallId: 'left-bottom', frame: 220, flashDuration: 6, rippleDuration: 15 },
  { wallId: 'bottom', frame: 260, flashDuration: 6, rippleDuration: 15 },
];

// ── Terminal content ──
export const TERMINAL_LINES = [
  { text: '$ pdd generate user_parser', color: TERMINAL_TEXT, delay: 0 },
  { text: '  Generating...', color: TERMINAL_TEXT, delay: 30 },
  { text: '  → parsing test_null_handling', color: TERMINAL_TEXT, delay: 50 },
  { text: '  → parsing test_email_format', color: TERMINAL_TEXT, delay: 65 },
  { text: '  ✓ All 12 tests passing', color: TERMINAL_GREEN, delay: 90 },
];

// ── Font ──
export const MONO_FONT = 'JetBrains Mono, Menlo, Monaco, monospace';

// ── Particle config ──
export const PARTICLE_COUNT = 220;
export const NOISE_SCALE = 0.04;
export const NOISE_SPEED = 0.03;
