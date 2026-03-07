// Closing05SplitDarningVsMolding constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 240;

// Panel layout
export const LEFT_PANEL = { x: 0, y: 100, w: 940, h: 880 };
export const RIGHT_PANEL = { x: 980, y: 100, w: 940, h: 880 };
export const DIVIDER_X = 960;
export const PANEL_RADIUS = 12;

// Colors — Red (left / darning)
export const RED = "#EF4444";
export const RED_BG = "rgba(239, 68, 68, 0.06)";

// Colors — Green (right / molding)
export const GREEN = "#22C55E";
export const GREEN_BG = "rgba(34, 197, 94, 0.06)";

// Colors — Neutral
export const PANEL_BG = "rgba(15, 23, 42, 0.88)";
export const MUTED_TEXT = "#94A3B8";
export const FOOTER_COLOR = "#FFFFFF";
export const BG_COLOR = "#0A1628";

// Font
export const FONT_FAMILY = "'Inter', sans-serif";

// Animation timing (frames at 30fps)
export const PANEL_SLIDE_END = 22;

export const DIVIDER_FADE_START = 12;
export const DIVIDER_FADE_END = 25;

export const LEFT_HEADER_FADE_START = 22;
export const LEFT_HEADER_FADE_END = 38;

export const LEFT_CURVE_DRAW_START = 30;
export const LEFT_CURVE_DRAW_END = 55;

export const RIGHT_HEADER_FADE_START = 38;
export const RIGHT_HEADER_FADE_END = 54;

export const RIGHT_CURVE_DRAW_START = 46;
export const RIGHT_CURVE_DRAW_END = 65;

export const OUTCOME_FADE_START = 60;
export const OUTCOME_FADE_END = 78;

export const FOOTER_FADE_START = 75;
export const FOOTER_FADE_END = 95;

export const FADEOUT_START = 195;
export const FADEOUT_END = 240;

// Spring config
export const PANEL_SPRING = { damping: 16, stiffness: 160 };

// Cost curve chart area (relative to panel)
export const CURVE_PADDING_X = 60;
export const CURVE_PADDING_TOP = 20;
export const CURVE_WIDTH = 300;
export const CURVE_HEIGHT = 120;
