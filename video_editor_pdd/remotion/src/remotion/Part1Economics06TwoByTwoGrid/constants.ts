// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0D1117";

// Grid area
export const GRID_X = 640;
export const GRID_Y = 180;
export const GRID_W = 640;
export const GRID_H = 640;

// Derived grid positions
export const GRID_CENTER_X = GRID_X + GRID_W / 2; // 960
export const GRID_CENTER_Y = GRID_Y + GRID_H / 2; // 500
export const GRID_RIGHT = GRID_X + GRID_W; // 1280
export const GRID_BOTTOM = GRID_Y + GRID_H; // 820

// Quadrant centers
export const TL_CENTER_X = GRID_X + GRID_W / 4; // 800
export const TL_CENTER_Y = GRID_Y + GRID_H / 4; // 340
export const TR_CENTER_X = GRID_X + (3 * GRID_W) / 4; // 1120
export const TR_CENTER_Y = GRID_Y + GRID_H / 4; // 340
export const BL_CENTER_X = GRID_X + GRID_W / 4; // 800
export const BL_CENTER_Y = GRID_Y + (3 * GRID_H) / 4; // 660
export const BR_CENTER_X = GRID_X + (3 * GRID_W) / 4; // 1120
export const BR_CENTER_Y = GRID_Y + (3 * GRID_H) / 4; // 660

// Colors
export const BORDER_COLOR = "#334155";
export const GREEN = "#5AAA6E";
export const RED = "#E74C3C";
export const AMBER = "#D9944A";
export const LABEL_MUTED = "#94A3B8";
export const SUMMARY_COLOR = "#E2E8F0";

// Typography
export const FONT_FAMILY = "Inter, sans-serif";

// Enterprise circle
export const ENTERPRISE_CIRCLE_RADIUS = 100;

// Animation timing (frames at 30fps)
export const GRID_DRAW_START = 30;
export const GRID_DRAW_END = 90;

export const TL_GLOW_START = 90;
export const TL_GLOW_END = 110;
export const TL_STAT_START = 100;
export const TL_STAT_END = 120;

export const BR_GLOW_START = 180;
export const BR_GLOW_END = 200;
export const BR_STAT_START = 190;
export const BR_STAT_END = 210;

export const AMBER_START = 270;
export const AMBER_END = 290;

export const CIRCLE_DRAW_START = 330;
export const CIRCLE_DRAW_END = 355;
export const CIRCLE_LABEL_START = 345;
export const CIRCLE_LABEL_END = 365;

export const SUMMARY_FADE_START = 420;
export const SUMMARY_FADE_END = 440;

export const TOTAL_FRAMES = 750;
