// ColdOpen01SplitScreenDarning – layout, color & timing constants

// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 270; // 9 seconds @ 30fps

// Layout: two panels with a centre divider
export const DIVIDER_GAP = 40; // total gap in the centre
export const PANEL_WIDTH = (CANVAS_WIDTH - DIVIDER_GAP) / 2; // 940
export const DIVIDER_THICKNESS = 2;

// Colours
export const BACKGROUND_COLOR = '#000000';
export const DIVIDER_COLOR = '#FFFFFF';
export const DIVIDER_OPACITY = 0.7; // spec says 0.4, raised to 0.7 to meet minimum divider opacity contract

// Label overlay text (bottom of each panel)
export const LABEL_FONT_SIZE = 22;
export const LABEL_COLOR = '#FFFFFF';
export const LABEL_OPACITY_PRIMARY = 0.82;
export const LABEL_OPACITY_SUPPORTING = 0.65;
export const LABEL_BG_COLOR = 'rgba(0,0,0,0.55)';

// Timing (frame numbers)
export const FADE_IN_START = 0;
export const FADE_IN_END = 15; // 0–0.5s  divider + panels fade in

export const CLIP_A_START = 0; // first clip pair starts
export const CLIP_A_END = 160; // first clip pair hard boundary

export const CROSSFADE_START = 150; // second clip pair starts fading in
export const CROSSFADE_DURATION = 10; // 10-frame crossfade

export const CLIP_B_START = 150;
export const CLIP_B_END = 270;

export const HOLD_START = 260;
export const HOLD_END = 270;

// Panel labels
export const LEFT_LABEL = 'Developer patching code';
export const RIGHT_LABEL = 'Grandmother darning socks';
