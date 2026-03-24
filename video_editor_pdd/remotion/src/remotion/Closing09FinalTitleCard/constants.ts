// Closing09FinalTitleCard constants

// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BG_COLOR = '#0A0F1A';

// Ghost triangle
export const TRIANGLE_CENTER: [number, number] = [960, 390];
export const TRIANGLE_VERTICES: [number, number][] = [
  [960, 320],
  [860, 450],
  [1060, 450],
];
export const TRIANGLE_EDGE_COLOR = '#334155';
export const TRIANGLE_EDGE_OPACITY = 0.02;
export const TRIANGLE_EDGE_WIDTH = 1;
export const NODE_RADIUS = 8;
export const NODE_COLORS = ['#60A5FA', '#4ADE80', '#D9944A'] as const;
export const NODE_OPACITY = 0.03;

// Title
export const TITLE_TEXT = 'Prompt-Driven Development';
export const TITLE_Y = 400;
export const TITLE_FONT_SIZE = 52;
export const TITLE_COLOR = '#E2E8F0';
export const TITLE_OPACITY = 1;
export const TITLE_LETTER_SPACING = 2;
export const TITLE_GLOW_COLOR = '#D9944A';
export const TITLE_GLOW_OPACITY = 0.08;
export const TITLE_GLOW_BLUR = 60;

// Command block
export const CMD_BLOCK_Y = 580;
export const CMD_BLOCK_WIDTH = 480;
export const CMD_BORDER_LEFT_WIDTH = 2;
export const CMD_BORDER_LEFT_COLOR = '#D9944A';
export const CMD_BORDER_LEFT_OPACITY = 0.2;
export const CMD_FONT_SIZE = 16;
export const CMD_LINE_HEIGHT = 30;
export const CMD_TEXT_COLOR = '#64748B';
export const CMD_TEXT_OPACITY = 0.5;

// Command lines
export const CMD_LINE_1 = 'uv tool install pdd-cli';
export const CMD_LINE_2 = 'pdd update your_module.py';

// URL
export const URL_TEXT = 'promptdrivendevelopment.com';
export const URL_Y = 480;
export const URL_FONT_SIZE = 16;
export const URL_COLOR = '#94A3B8';
export const URL_OPACITY = 0.6;

// Animation timing (frames)
export const TOTAL_FRAMES = 240;
export const GHOST_FADE_START = 0;
export const GHOST_FADE_DURATION = 30;
export const TITLE_FADE_START = 0;
export const TITLE_FADE_DURATION = 30;
export const URL_FADE_START = 30;
export const URL_FADE_DURATION = 15;
export const CMD_BLOCK_FADE_START = 45;
export const CMD_LINE_FADE_DURATION = 15;
export const CMD_LINE_2_FADE_START = 55;
