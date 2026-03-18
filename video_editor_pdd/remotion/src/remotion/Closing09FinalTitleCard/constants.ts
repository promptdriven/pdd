// Closing09FinalTitleCard constants

// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BG_COLOR = '#060A12';

// Ghost triangle
export const TRIANGLE_CENTER: [number, number] = [960, 520];
export const TRIANGLE_VERTICES: [number, number][] = [
  [960, 280],
  [710, 713],
  [1210, 713],
];
export const TRIANGLE_EDGE_COLOR = '#1E293B';
export const TRIANGLE_EDGE_OPACITY = 0.04;
export const TRIANGLE_EDGE_WIDTH = 1;
export const NODE_RADIUS = 8;
export const NODE_COLORS = ['#4A90D9', '#D9944A', '#5AAA6E'] as const;
export const NODE_OPACITY = 0.02;

// Title
export const TITLE_TEXT = 'Prompt-Driven Development';
export const TITLE_Y = 380;
export const TITLE_FONT_SIZE = 48;
export const TITLE_COLOR = '#E2E8F0';
export const TITLE_OPACITY = 0.85;
export const TITLE_LETTER_SPACING = 1;

// Command block
export const CMD_BLOCK_Y = 520;
export const CMD_BLOCK_WIDTH = 480;
export const CMD_BLOCK_BG = '#0F172A';
export const CMD_BLOCK_BG_OPACITY = 0.4;
export const CMD_BLOCK_BORDER_RADIUS = 8;
export const CMD_BLOCK_PADDING_V = 24;
export const CMD_BLOCK_PADDING_H = 32;
export const CMD_BORDER_LEFT_WIDTH = 2;
export const CMD_BORDER_LEFT_COLOR = '#4A90D9';
export const CMD_BORDER_LEFT_OPACITY = 0.15;
export const CMD_FONT_SIZE = 15;
export const CMD_LINE_HEIGHT = 28;
export const CMD_TEXT_COLOR = '#E2E8F0';
export const CMD_TEXT_OPACITY = 0.7;
export const CMD_PROMPT_COLOR = '#64748B';
export const CMD_PROMPT_OPACITY = 0.4;
export const CMD_KEYWORD_COLOR = '#4A90D9';
export const CMD_KEYWORD_OPACITY = 0.8;

// Command lines
export const CMD_LINE_1 = '$ uv tool install pdd-cli';
export const CMD_LINE_2 = '$ pdd update your_module.py';

// URL
export const URL_TEXT = 'pdd.dev';
export const URL_Y = 660;
export const URL_FONT_SIZE = 20;
export const URL_COLOR = '#4A90D9';
export const URL_OPACITY = 0.6;
export const URL_UNDERLINE_OPACITY = 0.1;

// Animation timing (frames)
export const TOTAL_FRAMES = 240;

// Phase 1: Ghost triangle fade-in (frame 0-30)
export const GHOST_FADE_START = 0;
export const GHOST_FADE_DURATION = 25;

// Phase 2: Title fade-in (frame 30-55)
export const TITLE_FADE_START = 30;
export const TITLE_FADE_DURATION = 25;

// Phase 3: Command block (frame 70-120)
export const CMD_BLOCK_FADE_START = 70;
export const CMD_BLOCK_BG_FADE_DURATION = 15;
export const CMD_TYPE_FRAMES_PER_CHAR = 2;
export const CMD_LINE_1_TYPE_START = 85; // after bg fades in
export const CMD_LINE_2_DELAY = 20; // frames after line 1 finishes

// Phase 4: URL fade-in (frame 120-138)
export const URL_FADE_START = 120;
export const URL_FADE_DURATION = 18;
