// ── Canvas ──
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 240;

// ── Colors ──
export const BG = '#0A0F1A';
export const BLOCK_FILL = '#1E293B';
export const EDGE_COLOR = '#334155';
export const SELECTION_BLUE = '#4A90D9';
export const EDITOR_BG = '#0F172A';
export const TEXT_LIGHT = '#E2E8F0';
export const TEXT_MUTED = '#CBD5E1';
export const TERMINAL_TEXT = '#94A3B8';
export const SUCCESS_GREEN = '#5AAA6E';

// ── Selected Module ──
export const MODULE_POS = { x: 640, y: 420 };
export const MODULE_SIZE = { w: 120, h: 60 };

// ── Prompt Document ──
export const PROMPT_POS = { x: 1100, y: 380 };
export const PROMPT_SIZE = { w: 280, h: 200 };
export const TITLE_BAR_H = 20;

// ── Terminal ──
export const TERMINAL_POS = { x: 1400, y: 860 };
export const TERMINAL_SIZE = { w: 420, h: 140 };

// ── Particle Stream ──
export const PARTICLE_COUNT = 25;
export const PARTICLE_SIZE = 3;

// ── Prompt content lines ──
export const PROMPT_LINES = [
  '# Auth Handler',
  'Authenticate incoming requests using JWT.',
  'Validate token signature and expiration.',
  'Extract user_id and role from claims.',
  'Return None on invalid or expired tokens.',
  'Check token against revocation list.',
  'Support both Bearer and cookie auth.',
  'Log failed auth attempts with IP.',
  'Rate-limit failed attempts per source.',
  'Return 401 with clear error message.',
  'Handle missing Authorization header.',
  'Cache validated tokens for 60 seconds.',
];

// ── Codebase background block positions (simplified topology) ──
export const CODEBASE_BLOCKS: Array<{ x: number; y: number; w: number; h: number }> = [
  { x: 200, y: 160, w: 100, h: 50 },
  { x: 380, y: 120, w: 90, h: 45 },
  { x: 540, y: 200, w: 110, h: 55 },
  { x: 300, y: 300, w: 95, h: 48 },
  { x: 480, y: 340, w: 105, h: 52 },
  { x: 640, y: 420, w: 120, h: 60 }, // The selected module
  { x: 800, y: 300, w: 100, h: 50 },
  { x: 750, y: 480, w: 90, h: 45 },
  { x: 420, y: 500, w: 100, h: 50 },
  { x: 260, y: 460, w: 85, h: 42 },
  { x: 150, y: 340, w: 95, h: 48 },
  { x: 560, y: 560, w: 110, h: 55 },
  { x: 700, y: 160, w: 100, h: 50 },
  { x: 850, y: 200, w: 90, h: 45 },
  { x: 350, y: 580, w: 80, h: 40 },
  { x: 180, y: 560, w: 100, h: 50 },
  { x: 900, y: 420, w: 85, h: 42 },
  { x: 500, y: 120, w: 70, h: 35 },
];

// ── Codebase edges (index pairs referencing CODEBASE_BLOCKS) ──
export const CODEBASE_EDGES: Array<[number, number]> = [
  [0, 1], [1, 2], [0, 3], [3, 4], [4, 5],
  [2, 6], [5, 7], [5, 8], [8, 9], [9, 10],
  [7, 11], [2, 12], [12, 13], [8, 14], [14, 15],
  [6, 16], [1, 17],
];

// ── Terminal lines ──
export const TERMINAL_CMD = '$ pdd update auth_handler.py';
export const TERMINAL_ANALYZING = 'Analyzing module... extracting intent...';
export const TERMINAL_SUCCESS = '✓ Created auth_handler.prompt';
