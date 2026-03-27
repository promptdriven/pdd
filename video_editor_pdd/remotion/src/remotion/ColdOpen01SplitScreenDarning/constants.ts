// ColdOpen01SplitScreenDarning – layout & color constants

/** Canvas */
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

/** Total duration in frames (30 fps × 9s) */
export const TOTAL_FRAMES = 270;

/** Panel layout */
export const PANEL_WIDTH = 940;
export const DIVIDER_GAP = 40; // px between the two panels
export const DIVIDER_THICKNESS = 2;
export const DIVIDER_COLOR = "#FFFFFF";
export const DIVIDER_MAX_OPACITY = 0.7;

/** Background behind the divider strip */
export const BG_COLOR = "#000000";

/** Timing (frames) */
export const FADE_IN_END = 15; // divider + panels fade in over 0-15
export const CLIP_A_END = 160; // first clip pair ends
export const CROSSFADE_START = 150; // second clip pair begins (10-frame overlap)
export const CROSSFADE_DURATION = 10;
export const HOLD_START = 260; // final hold begins
