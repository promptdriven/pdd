// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = "#0A0F1A";

// Grid
export const GRID_SIZE = 600;
export const CELL_SIZE = GRID_SIZE / 2; // 300
export const GRID_CENTER_X = 960;
export const GRID_CENTER_Y = 480;
export const GRID_LEFT = GRID_CENTER_X - GRID_SIZE / 2;
export const GRID_TOP = GRID_CENTER_Y - GRID_SIZE / 2;
export const GRID_LINE_COLOR = "#334155";
export const GRID_LINE_WIDTH = 2;

// Quadrant colors
export const GREEN_QUADRANT_COLOR = "#5AAA6E";
export const GREEN_FILL_OPACITY = 0.15;
export const GREEN_GLOW_OPACITY = 0.3;

export const RED_QUADRANT_COLOR = "#EF4444";
export const RED_FILL_OPACITY = 0.15;
export const RED_GLOW_OPACITY = 0.3;

export const NEUTRAL_COLOR = "#64748B";
export const NEUTRAL_FILL_OPACITY = 0.06;

// Typography colors
export const AXIS_LABEL_COLOR = "#94A3B8";
export const INSIGHT_TEXT_COLOR = "#E2E8F0";

// Typography sizes
export const AXIS_LABEL_SIZE = 16;
export const QUADRANT_LABEL_SIZE = 20;
export const INSIGHT_TEXT_SIZE = 16;

// Insight text position
export const INSIGHT_Y = 830;

// Animation timing (frames)
export const GRID_DRAW_START = 0;
export const GRID_DRAW_END = 45;
export const GREEN_QUADRANT_START = 45;
export const GREEN_QUADRANT_END = 90;
export const GREEN_HOLD_END = 150;
export const RED_QUADRANT_START = 150;
export const RED_QUADRANT_END = 210;
export const BOTH_GLOW_END = 390;
export const INSIGHT_FADE_START = 390;
export const INSIGHT_FADE_END = 420;
export const TOTAL_FRAMES = 630;

// Type-in speed
export const FRAMES_PER_CHAR = 2;

// Easing durations
export const GRID_DRAW_DURATION = 45;
export const QUADRANT_FILL_DURATION = 30;
export const INSIGHT_FADE_DURATION = 30;
