// === Canvas ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 600;

// === Layout ===
export const DIVIDER_WIDTH = 2;
export const DIVIDER_GAP = 40; // total gap in center
export const PANEL_WIDTH = 940;
export const PANEL_LEFT_X = 0;
export const PANEL_RIGHT_X = PANEL_WIDTH + DIVIDER_GAP;

// === Colors ===
export const BACKGROUND_COLOR = '#000000';
export const DIVIDER_COLOR = '#FFFFFF';
export const DIVIDER_OPACITY = 0.7;

export const AURA_AMBER = '#D9944A';
export const AURA_BLUE = '#4A90D9';
export const AURA_MAX_OPACITY = 0.3;

// Intensified aura phase
export const AURA_INTENSE_AMBER = '#E8A85C';
export const AURA_INTENSE_BLUE = '#5CA0E8';
export const AURA_INTENSE_OPACITY = 0.55;

// === Labels ===
export const LABEL_LEFT = 'Craftsman — value in the object';
export const LABEL_RIGHT = 'Mold — value in the specification';
export const LABEL_FONT_SIZE = 22;
export const LABEL_PRIMARY_OPACITY = 0.85;
export const LABEL_APPEAR_FRAME = 90;

// === Animation Timing (frames) ===
// Phase 1: Fade in (0–15)
export const FADE_IN_START = 0;
export const FADE_IN_END = 15;

// Phase 2: Establishing contrast (15–120)
export const ESTABLISH_START = 15;
export const ESTABLISH_END = 120;

// Phase 3: Aura appear (120–240)
export const AURA_APPEAR_START = 120;
export const AURA_APPEAR_END = 240;

// Phase 4: Aura intensify (240–360)
export const AURA_INTENSIFY_START = 240;
export const AURA_INTENSIFY_END = 360;

// Phase 5: Part dissolve & reappear (360–480)
export const PART_DISSOLVE_START = 360;
export const PART_DISSOLVE_END = 390; // 30 frames dissolve
export const PART_REAPPEAR_BEAT = 420; // 30 frame pause after dissolve
export const PART_REAPPEAR_END = 440; // 20 frames reappear

// Phase 6: Hold & fade out (480–600)
export const HOLD_START = 480;
export const FADE_OUT_START = 570;
export const FADE_OUT_END = 600;
