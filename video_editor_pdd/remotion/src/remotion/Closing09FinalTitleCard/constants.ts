// Closing09FinalTitleCard — constants

// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BG_COLOR = '#060A12';

// Ghost Triangle
export const TRIANGLE_CENTER: [number, number] = [960, 520];
export const TRIANGLE_VERTICES: [number, number][] = [
  [960, 280],
  [710, 713],
  [1210, 713],
];
export const TRIANGLE_EDGE_COLOR = '#1E293B';
export const TRIANGLE_EDGE_OPACITY = 0.04;
export const TRIANGLE_EDGE_WIDTH = 1;
export const TRIANGLE_NODE_RADIUS = 8;
export const TRIANGLE_NODE_COLORS = ['#4A90D9', '#D9944A', '#5AAA6E'];
export const TRIANGLE_NODE_OPACITY = 0.02;

// Colors
export const TEXT_COLOR = '#E2E8F0';
export const ACCENT_BLUE = '#4A90D9';
export const PROMPT_GRAY = '#64748B';
export const COMMAND_BG = '#0F172A';

// Animation timing (frames)
export const GHOST_FADE_START = 0;
export const GHOST_FADE_END = 30;
export const TITLE_FADE_START = 30;
export const TITLE_FADE_DURATION = 25;
export const CMD_BLOCK_START = 70;
export const CMD_BG_FADE_DURATION = 15;
export const CMD_LINE1_DELAY = 15; // after CMD_BLOCK_START
export const CMD_LINE2_DELAY = 20; // after line1 finishes
export const CHARS_PER_2_FRAMES = 2; // 2 frames per character
export const URL_FADE_START = 120;
export const URL_FADE_DURATION = 18;

// Command strings
export const CMD_LINE1 = '$ uv tool install pdd-cli';
export const CMD_LINE2 = '$ pdd update your_module.py';
