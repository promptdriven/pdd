// constants.ts — Component-level constants for the 2×2 Study Grid

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 630;

// Background
export const BG_COLOR = "#0A0F1A";

// Grid layout
export const GRID_SIZE = 600;
export const CELL_SIZE = 300;
export const GRID_CENTER_X = 960;
export const GRID_CENTER_Y = 480;
export const GRID_LEFT = GRID_CENTER_X - GRID_SIZE / 2; // 660
export const GRID_TOP = GRID_CENTER_Y - GRID_SIZE / 2; // 180
export const GRID_RIGHT = GRID_LEFT + GRID_SIZE; // 1260
export const GRID_BOTTOM = GRID_TOP + GRID_SIZE; // 780

// Grid lines
export const GRID_LINE_COLOR = "#334155";
export const GRID_LINE_WIDTH = 2;

// Quadrant colors
export const GREEN_QUADRANT = "#5AAA6E";
export const GREEN_FILL_OPACITY = 0.15;
export const GREEN_GLOW_OPACITY = 0.3;

export const RED_QUADRANT = "#EF4444";
export const RED_FILL_OPACITY = 0.15;
export const RED_GLOW_OPACITY = 0.3;

export const NEUTRAL_FILL = "#64748B";
export const NEUTRAL_FILL_OPACITY = 0.06;

// Axis labels
export const AXIS_LABEL_COLOR = "#94A3B8";
export const AXIS_LABEL_SIZE = 16;

// Quadrant labels
export const QUADRANT_LABEL_SIZE = 20;

// Insight text
export const INSIGHT_COLOR = "#E2E8F0";
export const INSIGHT_SIZE = 16;
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

// Easing durations
export const GRID_DRAW_DURATION = 30;
export const QUADRANT_FILL_DURATION = 30;
export const LABEL_CHARS_PER_FRAME = 0.5; // 2 frames per character
export const INSIGHT_FADE_DURATION = 30;

// Axis data
export const X_LABELS = ["Greenfield", "Brownfield"] as const;
export const Y_LABELS = ["In-Distribution", "Out-of-Distribution"] as const;

// Quadrant data
export const GREEN_LABEL_TEXT = "GitHub study: +55%";
export const RED_LABEL_TEXT = "METR study: \u221219%";
export const INSIGHT_TEXT =
  "Every study is correct. They just measured different quadrants.";
