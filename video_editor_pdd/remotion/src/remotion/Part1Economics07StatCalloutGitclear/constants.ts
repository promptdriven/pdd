// Part1Economics07StatCalloutGitclear constants

// Animation timing (frames at 30fps)
export const CARD_SLIDE_IN_START = 0;
export const CARD_SLIDE_IN_END = 20;
export const HEADLINE_FADE_START = 15;
export const HEADLINE_FADE_END = 35;
export const CHURN_BAR_START = 30;
export const CHURN_BAR_END = 80;
export const REFACTOR_BAR_START = 60;
export const REFACTOR_BAR_END = 110;
export const SOURCE_FADE_START = 100;
export const SOURCE_FADE_END = 120;
export const HOLD_END = 240;
export const CARD_SLIDE_OUT_START = 240;
export const CARD_SLIDE_OUT_END = 300;
export const TOTAL_FRAMES = 300;

// Layout
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const CARD_X = 1020;
export const CARD_Y = 300;
export const CARD_WIDTH = 820;
export const CARD_HEIGHT = 420;
export const CARD_BORDER_RADIUS = 16;
export const ACCENT_BAR_WIDTH = 4;
export const BAR_TRACK_HEIGHT = 28;
export const BAR_TRACK_BORDER_RADIUS = 6;

// Colors
export const BG_COLOR = "#0A1628";
export const CARD_BG = "rgba(15, 23, 42, 0.88)";
export const ACCENT_RED = "#EF4444";
export const ACCENT_AMBER = "#F59E0B";
export const ACCENT_DEEP_RED = "#DC2626";
export const BAR_TRACK_BG = "rgba(239, 68, 68, 0.15)";
export const WHITE = "#FFFFFF";
export const LABEL_COLOR = "#CBD5E1";
export const STAT_VALUE_COLOR = "#EF4444";
export const SOURCE_COLOR = "#64748B";

// Stat bar data
export const CHURN_GRADIENT = ["#EF4444", "#F59E0B"] as const;
export const REFACTOR_GRADIENT = ["#EF4444", "#DC2626"] as const;
export const CHURN_FILL = 0.44;
export const REFACTOR_FILL = 0.60;

// Typography
export const HEADLINE_FONT_SIZE = 28;
export const LABEL_FONT_SIZE = 22;
export const STAT_FONT_SIZE = 40;
export const ARROW_SIZE = 24;
export const SOURCE_FONT_SIZE = 15;

// Animation
export const SLIDE_DISTANCE = 200;
export const BORDER_PULSE_SPEED = 0.07;
export const BORDER_PULSE_MIN = 0.3;
export const BORDER_PULSE_MAX = 0.6;
