// ─── Canvas ───
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 48;

// ─── Theme (Catppuccin Mocha) ───
export const BG_COLOR = "#1E1E2E";
export const LINE_NUMBER_COLOR = "#6C7086";
export const CURSOR_COLOR = "#CDD6F4";
export const TEXT_COLOR = "#CDD6F4";

// Syntax colours
export const KEYWORD_COLOR = "#CBA6F7"; // purple
export const FUNCTION_COLOR = "#89B4FA"; // blue
export const STRING_COLOR = "#A6E3A1"; // green
export const TYPE_COLOR = "#F9E2AF"; // yellow
export const OPERATOR_COLOR = "#89DCEB"; // teal
export const COMMENT_COLOR = "#6C7086"; // overlay1
export const NUMBER_COLOR = "#FAB387"; // peach
export const PARAM_COLOR = "#F38BA8"; // red (for variable names that are params)
export const VARIABLE_COLOR = "#CDD6F4"; // text

// Patch-comment colours
export const PATCH_COMMENT_COLOR = "#6C7086";
export const TODO_COMMENT_COLOR = "#F9E2AF";
export const HOTFIX_COMMENT_COLOR = "#F38BA8";

// Patch age left-border colours
export const RECENT_PATCH_COLOR = "#A6E3A1";
export const RECENT_PATCH_OPACITY = 0.15;
export const MEDIUM_PATCH_COLOR = "#F9E2AF";
export const MEDIUM_PATCH_OPACITY = 0.05;
export const OLD_PATCH_COLOR = "#A6E3A1";
export const OLD_PATCH_OPACITY = 0.05;

// ─── Layout ───
export const LINE_HEIGHT = 22;
export const FONT_SIZE = 14;
export const LINE_NUMBER_FONT_SIZE = 12;
export const GUTTER_WIDTH = 60;
export const CODE_LEFT_PADDING = 16;
export const EDITOR_TOP_PADDING = 24;
export const PATCH_BORDER_WIDTH = 3;

// ─── Cursor ───
export const CURSOR_LINE = 23; // 1-indexed
export const CURSOR_COLUMN = 4;
export const CURSOR_BLINK_FRAMES = 15; // 500ms at 30fps

// ─── Animation ───
export const FADE_IN_DURATION = 10; // frames
