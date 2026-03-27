// === Layout ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 600;
export const FPS = 30;

export const DIVIDER_WIDTH_PX = 2;
export const DIVIDER_GAP = 40; // total gap between panels
export const PANEL_WIDTH = 940; // (1920 - 40) / 2

// === Colors ===
export const BG_COLOR = '#000000';
export const DIVIDER_COLOR = '#FFFFFF';
export const DIVIDER_OPACITY = 0.7;

export const AURA_AMBER = '#D9944A';
export const AURA_BLUE = '#4A90D9';
export const AURA_MAX_OPACITY = 0.3;

// Intensified aura phase
export const AURA_INTENSE_AMBER = '#D9944A';
export const AURA_INTENSE_BLUE = '#4A90D9';
export const AURA_INTENSE_OPACITY = 0.55;

// === Labels ===
export const LEFT_LABEL = 'Craftsman — value in the object';
export const RIGHT_LABEL = 'Mold — value in the specification';
export const LABEL_FONT_SIZE = 22;
export const LABEL_PRIMARY_OPACITY = 0.82;

// === Timing (frames) ===
export const FADE_IN_START = 0;
export const FADE_IN_END = 15;

export const AURA_APPEAR_START = 120;
export const AURA_APPEAR_END = 180; // 60 frames build

export const AURA_INTENSIFY_START = 240;
export const AURA_INTENSIFY_END = 300; // 60 frames intensify

export const PART_DISSOLVE_START = 360;
export const PART_DISSOLVE_END = 390; // 30 frames dissolve
export const PART_REAPPEAR_START = 420; // 30-frame gap after dissolve
export const PART_REAPPEAR_END = 440; // 20 frames reappear

export const FADE_OUT_START = 570;
export const FADE_OUT_END = 600;
