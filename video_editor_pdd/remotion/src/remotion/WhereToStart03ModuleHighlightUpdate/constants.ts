// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BG_COLOR = '#0A0F1A';
export const TOTAL_FRAMES = 240;

// Colors
export const BLUE_ACCENT = '#4A90D9';
export const BLOCK_FILL = '#1E293B';
export const EDGE_COLOR = '#334155';
export const TEXT_LIGHT = '#E2E8F0';
export const TEXT_MUTED = '#CBD5E1';
export const TEXT_DIM = '#94A3B8';
export const TERMINAL_BG = '#0F172A';
export const EDITOR_BG = '#0F172A';
export const SUCCESS_GREEN = '#5AAA6E';

// Selected module block
export const MODULE_X = 640;
export const MODULE_Y = 420;
export const MODULE_W = 120;
export const MODULE_H = 60;

// Prompt document
export const PROMPT_X = 1100;
export const PROMPT_Y = 380;
export const PROMPT_W = 280;
export const PROMPT_H = 200;
export const PROMPT_TITLE_BAR_H = 20;

// Terminal
export const TERMINAL_X = 1400;
export const TERMINAL_Y = 860;
export const TERMINAL_W = 420;
export const TERMINAL_H = 140;

// Prompt file content lines
export const PROMPT_LINES = [
  '# Auth Handler',
  'Authenticate incoming requests using JWT.',
  'Validate token signature and expiration.',
  'Extract user_id and role from claims.',
  'Return None on invalid or expired tokens.',
  'Check token against revocation list.',
  'Support both Bearer and cookie tokens.',
  'Rate-limit failed auth attempts per IP.',
  'Log auth failures with request context.',
  'Return 401 with appropriate WWW-Authenticate.',
  'Handle token refresh for near-expiry tokens.',
  'Cache validated tokens for 30 seconds.',
];

// Codebase background blocks (simplified representation)
export const CODEBASE_BLOCKS: Array<{ x: number; y: number; w: number; h: number }> = [
  { x: 200, y: 180, w: 100, h: 50 },
  { x: 380, y: 140, w: 90, h: 45 },
  { x: 520, y: 260, w: 110, h: 55 },
  { x: 640, y: 420, w: 120, h: 60 }, // This is the selected module
  { x: 800, y: 300, w: 95, h: 48 },
  { x: 350, y: 350, w: 85, h: 42 },
  { x: 180, y: 480, w: 100, h: 50 },
  { x: 450, y: 520, w: 90, h: 45 },
  { x: 750, y: 500, w: 105, h: 52 },
  { x: 300, y: 620, w: 80, h: 40 },
  { x: 550, y: 650, w: 95, h: 48 },
  { x: 150, y: 320, w: 88, h: 44 },
  { x: 680, y: 180, w: 92, h: 46 },
  { x: 900, y: 450, w: 85, h: 42 },
  { x: 480, y: 400, w: 78, h: 39 },
];

// Codebase edges (connections between blocks by index)
export const CODEBASE_EDGES: Array<[number, number]> = [
  [0, 1], [1, 2], [2, 3], [3, 4], [5, 3],
  [6, 5], [7, 3], [8, 4], [9, 6], [10, 7],
  [11, 0], [12, 4], [13, 8], [14, 3],
];

// Terminal command text
export const TERMINAL_COMMAND = '$ pdd update auth_handler.py';
export const TERMINAL_ANALYZING = 'Analyzing module... extracting intent...';
export const TERMINAL_SUCCESS = '✓ Created auth_handler.prompt';

// Particle stream config
export const PARTICLE_COUNT = 25;
export const PARTICLE_SIZE = 3;
export const PARTICLE_STAGGER = 3;
