// Closing05SplitDarningVsMolding constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0A1628";

// Duration: 240 frames = 8s at 30fps
export const TOTAL_FRAMES = 240;
export const FPS = 30;

// Panel dimensions
export const PANEL_TOP = 100;
export const PANEL_BOTTOM = 980;
export const PANEL_HEIGHT = PANEL_BOTTOM - PANEL_TOP;

// Left panel: (0, 100) to (940, 980)
export const LEFT_PANEL_X = 0;
export const LEFT_PANEL_WIDTH = 940;

// Right panel: (980, 100) to (1920, 980)
export const RIGHT_PANEL_X = 980;
export const RIGHT_PANEL_WIDTH = 940;

// Divider
export const DIVIDER_X = 960;
export const DIVIDER_WIDTH = 2;

// Colors — Darning (red)
export const DARNING_COLOR = "#EF4444";
export const DARNING_BG = "rgba(239, 68, 68, 0.06)";
export const DARNING_ICON_OPACITY = 0.3;

// Colors — Molding (green)
export const MOLDING_COLOR = "#22C55E";
export const MOLDING_BG = "rgba(34, 197, 94, 0.06)";
export const MOLDING_ICON_OPACITY = 0.3;

// Colors — General
export const MUTED_TEXT_COLOR = "#94A3B8";
export const DIVIDER_COLOR = "rgba(255, 255, 255, 0.4)";
export const WHITE = "#FFFFFF";

// Typography
export const HEADER_FONT_SIZE = 28;
export const HEADER_LETTER_SPACING = "0.15em";
export const CURVE_LABEL_FONT_SIZE = 18;
export const OUTCOME_FONT_SIZE = 48;
export const FOOTER_FONT_SIZE = 28;

// Icon size
export const ICON_SIZE = 90;

// Slide distance (pixels)
export const SLIDE_DISTANCE = 960;

// Spring config for panel slides
export const SPRING_DAMPING = 16;
export const SPRING_STIFFNESS = 160;

// Animation timing (frames at 30fps)

// Panels slide in simultaneously
export const PANEL_SLIDE_IN_START = 0;
export const PANEL_SLIDE_IN_END = 22;

// Divider fades in
export const DIVIDER_FADE_START = 12;
export const DIVIDER_FADE_END = 25;

// Left header "DARNING" + icon fade in
export const LEFT_HEADER_START = 22;
export const LEFT_HEADER_END = 38;

// Left cost curve draws
export const LEFT_CURVE_START = 30;
export const LEFT_CURVE_END = 55;

// Right header "MOLDING" + icon fade in
export const RIGHT_HEADER_START = 38;
export const RIGHT_HEADER_END = 54;

// Right flat line draws
export const RIGHT_CURVE_START = 46;
export const RIGHT_CURVE_END = 65;

// Outcome words scale up
export const OUTCOME_START = 60;
export const OUTCOME_END = 78;

// Footer fades in
export const FOOTER_FADE_START = 75;
export const FOOTER_FADE_END = 95;

// Hold
export const HOLD_END = 195;

// Dissolve out
export const DISSOLVE_START = 195;
export const DISSOLVE_END = 240;

// Cost curve chart area (relative to panel)
export const CHART_LEFT = 80;
export const CHART_RIGHT = 860;
export const CHART_TOP = 380;
export const CHART_BOTTOM = 560;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;
