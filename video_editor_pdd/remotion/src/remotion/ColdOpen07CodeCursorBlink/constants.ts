// ColdOpen07CodeCursorBlink — constants
// Catppuccin Mocha inspired dark code editor theme

// === Canvas ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = '#1E1E2E';

// === Duration ===
export const TOTAL_FRAMES = 48;
export const FADE_IN_FRAMES = 10;

// === Editor Layout ===
export const GUTTER_WIDTH = 60;
export const LINE_HEIGHT = 22;
export const CODE_PADDING_TOP = 40;
export const CODE_PADDING_LEFT = 16;
export const CODE_FONT_SIZE = 14;
export const LINE_NUMBER_FONT_SIZE = 12;
export const FONT_FAMILY = '"JetBrains Mono", "Fira Code", "Cascadia Code", monospace';

// === Colors — Catppuccin Mocha ===
export const COLOR_LINE_NUMBER = '#6C7086';
export const COLOR_TEXT = '#CDD6F4';
export const COLOR_KEYWORD = '#CBA6F7';    // purple
export const COLOR_FUNCTION = '#89B4FA';   // blue
export const COLOR_STRING = '#A6E3A1';     // green
export const COLOR_TYPE = '#F9E2AF';       // yellow
export const COLOR_PARAM = '#FAB387';      // peach/orange
export const COLOR_OPERATOR = '#89DCEB';   // sky
export const COLOR_NUMBER = '#FAB387';     // peach
export const COLOR_COMMENT = '#6C7086';    // overlay0
export const COLOR_TODO_COMMENT = '#F9E2AF';   // yellow warning
export const COLOR_HOTFIX_COMMENT = '#F38BA8'; // red/pink

// === Cursor ===
export const CURSOR_COLOR = '#CDD6F4';
export const CURSOR_BLINK_FRAMES = 15; // 500ms at 30fps
export const CURSOR_LINE = 23;   // 1-indexed
export const CURSOR_COLUMN = 4;  // character offset
export const CURSOR_WIDTH = 9;   // block cursor width (approx 1 char)
export const CURSOR_HEIGHT = 18;

// === Patch age border colors ===
export const PATCH_RECENT_COLOR = '#A6E3A1';
export const PATCH_RECENT_OPACITY = 0.15;
export const PATCH_MEDIUM_COLOR = '#F9E2AF';
export const PATCH_MEDIUM_OPACITY = 0.05;
export const PATCH_OLD_COLOR = '#A6E3A1';
export const PATCH_OLD_OPACITY = 0.05;

// === Patch comment definitions ===
export interface PatchComment {
  line: number;
  text: string;
  age: 'old' | 'medium' | 'recent';
  commentType: 'patch' | 'todo' | 'hotfix';
}

export const PATCH_COMMENTS: PatchComment[] = [
  { line: 5, text: '# PATCH: fixed null check', age: 'old', commentType: 'patch' },
  { line: 12, text: '# TODO: refactor this block', age: 'old', commentType: 'todo' },
  { line: 18, text: '# HOTFIX: edge case #1247', age: 'medium', commentType: 'hotfix' },
  { line: 23, text: '# PATCH: handle empty list', age: 'recent', commentType: 'patch' },
  { line: 31, text: '# PATCH: timezone fix', age: 'medium', commentType: 'patch' },
  { line: 37, text: '# HOTFIX: race condition', age: 'recent', commentType: 'hotfix' },
];
