// Part5Compound08SplitPatchingVsPdd constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0A1628";

// Total duration: 360 frames = 12s at 30fps
export const TOTAL_FRAMES = 360;
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

// Colors — Patching (red)
export const PATCHING_COLOR = "#EF4444";
export const PATCHING_BG = "rgba(239, 68, 68, 0.06)";
export const PATCHING_ICON_OPACITY = 0.3;

// Colors — Generation (green)
export const GENERATION_COLOR = "#22C55E";
export const GENERATION_BG = "rgba(34, 197, 94, 0.06)";
export const GENERATION_ICON_OPACITY = 0.3;

// Colors — General
export const LABEL_COLOR = "#94A3B8";
export const FOOTER_COLOR = "#CBD5E1";
export const DIVIDER_COLOR = "rgba(255, 255, 255, 0.4)";

// Typography
export const HEADER_FONT_SIZE = 28;
export const HEADER_LETTER_SPACING = "0.15em";
export const TIMELINE_LABEL_FONT_SIZE = 18;
export const OUTCOME_FONT_SIZE = 24;
export const FOOTER_FONT_SIZE = 22;

// Icon size
export const ICON_SIZE = 100;

// Timeline chart
export const TIMELINE_MONTHS = 12;
export const TIMELINE_BAR_WIDTH = 36;
export const TIMELINE_BAR_GAP = 8;
export const TIMELINE_HEIGHT = 160;
export const TIMELINE_WIDTH = TIMELINE_MONTHS * (TIMELINE_BAR_WIDTH + TIMELINE_BAR_GAP);

// Data
export const PATCHING_HEADER = "PATCHING";
export const GENERATION_HEADER = "GENERATION";
export const PATCHING_TIMELINE_LABEL = "Debt accumulates";
export const GENERATION_TIMELINE_LABEL = "Debt resets each cycle";
export const PATCHING_OUTCOME = "Fragile, slow, expensive";
export const GENERATION_OUTCOME = "Fresh, fast, compounding";
export const FOOTER_TEXT = "The approach you choose compounds over time";

// Animation timing (frames at 30fps)
// Panels slide in
export const PANEL_SLIDE_IN_START = 0;
export const PANEL_SLIDE_IN_END = 25;

// Divider fade in
export const DIVIDER_FADE_START = 15;
export const DIVIDER_FADE_END = 30;

// Left header + icon
export const LEFT_HEADER_START = 25;
export const LEFT_HEADER_END = 45;

// Left timeline bars animate
export const LEFT_TIMELINE_START = 35;
export const LEFT_TIMELINE_END = 55;

// Right header + icon
export const RIGHT_HEADER_START = 45;
export const RIGHT_HEADER_END = 65;

// Right timeline draws
export const RIGHT_TIMELINE_START = 55;
export const RIGHT_TIMELINE_END = 75;

// Outcome labels
export const OUTCOME_FADE_START = 70;
export const OUTCOME_FADE_END = 90;

// Footer
export const FOOTER_FADE_START = 85;
export const FOOTER_FADE_END = 105;

// Hold
export const HOLD_END = 300;

// Slide out
export const SLIDE_OUT_START = 300;
export const SLIDE_OUT_END = 360;

// Slide distance (pixels)
export const SLIDE_DISTANCE = 960;

// Spring config for panel slides
export const SPRING_DAMPING = 16;
export const SPRING_STIFFNESS = 160;

// Timeline bar stagger (frames between each bar animation)
export const BAR_STAGGER = 3;
