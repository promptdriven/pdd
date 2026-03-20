// === Canvas ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 210;

// === Panel Layout ===
export const DIVIDER_X = 960;
export const DIVIDER_WIDTH = 2;
export const DIVIDER_COLOR = '#334155';
export const DIVIDER_OPACITY = 0.4;

// === Background Colors ===
export const LEFT_BG = '#0D1117';
export const RIGHT_BG = '#1A1410';

// === Left Panel — Codebase ===
export const CODE_BLOCK_WIDTH = 40;
export const CODE_BLOCK_HEIGHT = 24;
export const CODE_BLOCK_FILL = '#161B22';
export const CODE_BLOCK_BORDER = '#30363D';
export const CODE_BLOCK_BORDER_OPACITY = 0.5;
export const DIFF_RED = '#F85149';
export const DIFF_GREEN = '#3FB950';
export const DIFF_MARKER_PERCENT = 60;
export const GLOW_RED_OPACITY = 0.04;
export const COMMENT_COLOR = '#8B949E';
export const COMMENT_OPACITY = 0.35;
export const COMMENT_FONT_SIZE = 11;
export const PATCH_COUNTER_COLOR = '#F85149';
export const PATCH_COUNTER_OPACITY = 0.85;
export const COUNTER_FONT_SIZE = 28;
export const COUNTER_SUFFIX_FONT_SIZE = 16;
export const COUNTER_SUFFIX_OPACITY = 0.6;

// === Right Panel — Garments ===
export const DRAWER_WOOD_COLOR = '#8B6D4B';
export const STITCH_COLOR = '#D9944A';
export const GARMENT_COUNTER_COLOR = '#D9944A';
export const GARMENT_COUNTER_OPACITY = 0.85;

// === Garment colors ===
export const GARMENT_FILLS = ['#F5F0E8', '#1E3A5F', '#9CA3AF', '#6B4E3D', '#4A3728'];

// === Floating comments ===
export const FLOATING_COMMENTS = [
  '// TODO: refactor',
  '// HACK',
  '// fixed null case',
  '// workaround for #412',
  '// legacy \u2014 do not touch',
  '// temporary fix 2023-04',
];

// === Garment types ===
export const GARMENT_TYPES = ['sock', 'shirt', 'trouser', 'sock', 'sweater'];

// === Animation timing ===
export const ZOOM_START = 10;
export const ZOOM_END = 90;
export const ZOOM_FROM = 1.0;
export const ZOOM_TO = 0.15;
export const COMMENTS_START = 90;
export const COMMENTS_DURATION = 50;
export const COUNTER_START = 140;
export const COUNTER_DURATION = 40;
export const PULSE_START = 180;
export const PULSE_DURATION = 30;

// === Counter targets ===
export const PATCH_COUNT_TARGET = 1247;
export const GARMENT_COUNT_TARGET = 47;

// === Code block grid layout ===
export const CODE_BLOCK_COLS = 10;
export const CODE_BLOCK_ROWS = 8;
export const CODE_BLOCK_GAP_X = 8;
export const CODE_BLOCK_GAP_Y = 6;

// === Seeded pseudo-random for reproducible layouts ===
export function seededRandom(seed: number): number {
  const x = Math.sin(seed * 9301 + 49297) * 49311;
  return x - Math.floor(x);
}
