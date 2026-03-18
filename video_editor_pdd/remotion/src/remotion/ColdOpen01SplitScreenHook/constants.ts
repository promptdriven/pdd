// Layout
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const SPLIT_X = 960;
export const DIVIDER_WIDTH = 2;
export const LEFT_PANEL_WIDTH = SPLIT_X - DIVIDER_WIDTH / 2; // 959
export const RIGHT_PANEL_X = SPLIT_X + DIVIDER_WIDTH / 2; // 961
export const RIGHT_PANEL_WIDTH = CANVAS_WIDTH - RIGHT_PANEL_X; // 959

// Duration
export const TOTAL_FRAMES = 240;
export const FPS = 30;

// Colors
export const BG_COLOR = '#000000';
export const DIVIDER_COLOR = '#334155';
export const DIVIDER_OPACITY = 0.12;

// Left panel (Developer / 2025)
export const LEFT_LABEL = '2025';
export const LEFT_LABEL_COLOR = '#4A90D9';
export const LEFT_COLOR_GRADE = '#4A90D9';
export const LEFT_COLOR_GRADE_OPACITY = 0.02;
export const LEFT_VIGNETTE_EDGE = '#000510';
export const LEFT_VIGNETTE_OPACITY = 0.2;

// Right panel (Grandmother / 1955)
export const RIGHT_LABEL = '1955';
export const RIGHT_LABEL_COLOR = '#D9944A';
export const RIGHT_COLOR_GRADE = '#D4A043';
export const RIGHT_COLOR_GRADE_OPACITY = 0.04;
export const RIGHT_VIGNETTE_EDGE = '#0A0500';
export const RIGHT_VIGNETTE_OPACITY = 0.2;

// Typography
export const LABEL_FONT_SIZE = 11;
export const LABEL_FONT_WEIGHT = 600;
export const LABEL_LETTER_SPACING = 3;
export const LABEL_Y = 36;
export const LABEL_BASE_OPACITY = 0.25;

// Animation phases (frame ranges)
export const PHASE_REVEAL_END = 10;
export const PHASE_WORK_END = 90;
export const PHASE_COMPLETE_END = 150;
export const PHASE_HOLD_END = 210;
export const PHASE_PULSE_END = 240;

// Label pulse animation
export const PULSE_CYCLE_FRAMES = 30;
export const PULSE_MIN_OPACITY = 0.25;
export const PULSE_MAX_OPACITY = 0.35;
