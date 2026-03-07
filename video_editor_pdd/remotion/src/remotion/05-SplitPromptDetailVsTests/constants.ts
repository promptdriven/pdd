// Part4Precision05SplitPromptDetailVsTests constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 360;

// Panel layout
export const LEFT_PANEL = { x: 0, y: 100, w: 940, h: 880 };
export const RIGHT_PANEL = { x: 980, y: 100, w: 940, h: 880 };
export const DIVIDER_X = 960;
export const PANEL_RADIUS = 12;

// Colors — Amber (left / prompt)
export const AMBER = "#F59E0B";
export const AMBER_MUTED = "#FCD34D";
export const AMBER_BG = "rgba(245, 158, 11, 0.06)";
export const AMBER_PILL_BG = "rgba(245, 158, 11, 0.15)";

// Colors — Green (right / tests)
export const GREEN = "#22C55E";
export const GREEN_MUTED = "#86EFAC";
export const GREEN_BG = "rgba(34, 197, 94, 0.06)";
export const GREEN_PILL_BG = "rgba(34, 197, 94, 0.15)";

// Colors — Neutral
export const PANEL_BG = "rgba(15, 23, 42, 0.88)";
export const SUBTEXT_COLOR = "#94A3B8";
export const FOOTER_COLOR = "#CBD5E1";

// Animation timing (frames at 30fps)
export const LEFT_SLIDE_IN_START = 0;
export const LEFT_SLIDE_IN_END = 25;
export const RIGHT_SLIDE_IN_START = 0;
export const RIGHT_SLIDE_IN_END = 25;

export const DIVIDER_FADE_START = 15;
export const DIVIDER_FADE_END = 30;

export const LEFT_HEADER_FADE_START = 25;
export const LEFT_HEADER_FADE_END = 45;

export const LEFT_STAT_FADE_START = 35;
export const LEFT_STAT_FADE_END = 55;

export const RIGHT_HEADER_FADE_START = 45;
export const RIGHT_HEADER_FADE_END = 65;

export const RIGHT_STAT_FADE_START = 55;
export const RIGHT_STAT_FADE_END = 75;

export const FOOTER_FADE_START = 70;
export const FOOTER_FADE_END = 90;

export const HOLD_END = 300;

export const FADEOUT_START = 300;
export const FADEOUT_END = 360;

// Spring config
export const PANEL_SPRING = { damping: 16, stiffness: 160 };
