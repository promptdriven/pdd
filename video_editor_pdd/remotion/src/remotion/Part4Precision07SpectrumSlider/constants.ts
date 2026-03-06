// Part4Precision07SpectrumSlider constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 750;

// Background
export const BG_COLOR = "#0A1628";

// Spectrum bar layout
export const BAR_X = 240;
export const BAR_Y = 420;
export const BAR_WIDTH = 1440;
export const BAR_HEIGHT = 12;
export const BAR_RADIUS = 6;

// Handle
export const HANDLE_SIZE = 24;
export const HANDLE_GLOW_RADIUS = 40;

// Tick marks
export const TICK_COUNT = 8;
export const TICK_WIDTH = 2;
export const TICK_HEIGHT = 20;
export const TICK_COLOR = "rgba(71, 85, 105, 0.4)";

// Spectrum positions (normalized 0-1)
export const CENTER_POS = 0.5;
export const LEFT_POS = 0.17;
export const RIGHT_POS = 0.83;

// Context cards
export const CARD_WIDTH = 400;
export const CARD_HEIGHT = 220;
export const CARD_Y = 520;
export const CARD_RADIUS = 12;

// Colors
export const BLUE = "#3B82F6";
export const AMBER = "#F59E0B";
export const GRAY = "#64748B";
export const BALANCED_DIM = "#94A3B8";
export const BALANCED_BRIGHT = "#CBD5E1";

export const BLUE_BG = "rgba(59, 130, 246, 0.12)";
export const BLUE_BORDER = "rgba(59, 130, 246, 0.3)";
export const AMBER_BG = "rgba(245, 158, 11, 0.12)";
export const AMBER_BORDER = "rgba(245, 158, 11, 0.3)";
export const TRACK_BG = "rgba(255, 255, 255, 0.1)";

// Animation timing (frames at 30fps)
export const BAR_FADE_START = 0;
export const BAR_FADE_END = 30;

export const LABELS_FADE_START = 20;
export const LABELS_FADE_END = 40;

export const TICKS_FADE_START = 30;
export const TICKS_FADE_END = 50;

export const HANDLE_APPEAR_START = 40;

export const HANDLE_SLIDE_LEFT_START = 60;
export const HANDLE_SLIDE_LEFT_END = 150;

export const GREENFIELD_CARD_START = 140;
export const GREENFIELD_CARD_FADE_IN_END = 180;
export const GREENFIELD_CARD_FADE_OUT_START = 340;
export const GREENFIELD_CARD_FADE_OUT_END = 360;

export const HANDLE_SLIDE_RIGHT_START = 320;
export const HANDLE_SLIDE_RIGHT_END = 420;

export const LEGACY_CARD_START = 400;
export const LEGACY_CARD_FADE_IN_END = 440;
export const LEGACY_CARD_FADE_OUT_START = 630;
export const LEGACY_CARD_FADE_OUT_END = 650;

export const HANDLE_SLIDE_CENTER_START = 650;
export const HANDLE_SLIDE_CENTER_END = 700;

export const BALANCED_BRIGHTEN_START = 680;
export const BALANCED_BRIGHTEN_END = 710;

export const SCENE_FADE_OUT_START = 700;
export const SCENE_FADE_OUT_END = 750;

// Typography
export const FONT_FAMILY = "Inter, sans-serif";
export const LABEL_FONT_SIZE = 18;
export const CARD_TITLE_SIZE = 24;
export const CARD_TRAITS_SIZE = 16;
export const LABEL_LETTER_SPACING = "0.15em";

// Spring configs
export const HANDLE_SPRING = { damping: 14, stiffness: 200 };
export const CARD_SPRING = { damping: 12, stiffness: 180 };
