// Part4Precision07SpectrumSlider constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0A1628";

// Spectrum bar layout
export const BAR_Y = 420;
export const BAR_X_START = 240;
export const BAR_X_END = 1680;
export const BAR_WIDTH = BAR_X_END - BAR_X_START; // 1440px
export const BAR_HEIGHT = 12;
export const BAR_RADIUS = 6;

// Handle
export const HANDLE_SIZE = 24;
export const HANDLE_GLOW_RADIUS = 40;

// Context cards
export const CARD_WIDTH = 400;
export const CARD_HEIGHT = 220;
export const CARD_Y = 520;

// Tick marks
export const TICK_COUNT = 8;
export const TICK_WIDTH = 2;
export const TICK_HEIGHT = 20;
export const TICK_COLOR = "#475569";
export const TICK_OPACITY = 0.4;

// Colors
export const BLUE = "#3B82F6";
export const GRAY = "#64748B";
export const AMBER = "#F59E0B";
export const WHITE = "#FFFFFF";
export const BALANCED_DIM = "#94A3B8";
export const BALANCED_BRIGHT = "#CBD5E1";

// Positions (normalized 0-1 along bar)
export const CENTER_POS = 0.5;
export const LEFT_POS = 0.17; // Greenfield position
export const RIGHT_POS = 0.83; // Legacy position

// Animation timing (frames at 30fps)
// Bar expand
export const BAR_FADE_START = 0;
export const BAR_FADE_END = 30;

// Labels fade in
export const LABELS_FADE_START = 20;
export const LABELS_FADE_END = 40;

// Tick marks fade in
export const TICKS_FADE_START = 30;
export const TICKS_FADE_END = 50;

// Handle appears at center
export const HANDLE_APPEAR_START = 40;

// Handle slides to left
export const HANDLE_SLIDE_LEFT_START = 60;
export const HANDLE_SLIDE_LEFT_END = 150;

// Greenfield card pop up
export const GREENFIELD_CARD_START = 140;
export const GREENFIELD_CARD_END = 180;

// Hold at left
// (frames 180-320)

// Handle slides left → right
export const HANDLE_SLIDE_RIGHT_START = 320;
export const HANDLE_SLIDE_RIGHT_END = 420;

// Greenfield card fade out
export const GREENFIELD_FADE_OUT_START = 340;
export const GREENFIELD_FADE_OUT_END = 360;

// Legacy card pop up
export const LEGACY_CARD_START = 400;
export const LEGACY_CARD_END = 440;

// Hold at right
// (frames 440-650)

// Handle slides back to center
export const HANDLE_SLIDE_CENTER_START = 650;
export const HANDLE_SLIDE_CENTER_END = 700;

// Legacy card fade out (before center return)
export const LEGACY_FADE_OUT_START = 640;
export const LEGACY_FADE_OUT_END = 660;

// Balanced label brightens
export const BALANCED_BRIGHTEN_START = 650;
export const BALANCED_BRIGHTEN_END = 700;

// Overall fade out
export const FADE_OUT_START = 700;
export const FADE_OUT_END = 750;

export const TOTAL_FRAMES = 750;
export const FPS = 30;

// Typography
export const FONT_FAMILY = "Inter, sans-serif";
