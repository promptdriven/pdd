// Part1Economics10SplitPerceptionReality constants

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

// Colors — Perception (green)
export const PERCEPTION_COLOR = "#22C55E";
export const PERCEPTION_BG = "rgba(34, 197, 94, 0.08)";
export const PERCEPTION_MUTED = "#86EFAC";
export const PERCEPTION_ICON_OPACITY = 0.3;

// Colors — Reality (red)
export const REALITY_COLOR = "#EF4444";
export const REALITY_BG = "rgba(239, 68, 68, 0.08)";
export const REALITY_MUTED = "#FCA5A5";
export const REALITY_ICON_OPACITY = 0.3;

// Colors — General
export const STAT_COLOR = "#FFFFFF";
export const SOURCE_COLOR = "#64748B";
export const DIVIDER_COLOR = "rgba(255, 255, 255, 0.4)";

// Typography
export const HEADER_FONT_SIZE = 28;
export const HEADER_LETTER_SPACING = "0.15em";
export const STAT_FONT_SIZE = 96;
export const DESCRIPTOR_FONT_SIZE = 24;
export const SOURCE_FONT_SIZE = 16;

// Arrow icon size
export const ARROW_SIZE = 80;

// Data
export const PERCEPTION_STAT_VALUE = 20;
export const PERCEPTION_STAT_PREFIX = "+";
export const PERCEPTION_STAT_SUFFIX = "%";
export const PERCEPTION_DESCRIPTOR = "faster (self-reported)";

export const REALITY_STAT_VALUE = 19;
export const REALITY_STAT_SUFFIX = "%";
export const REALITY_DESCRIPTOR = "slower (measured)";

export const SOURCE_TEXT = "METR Study, 2024";

// Animation timing (frames at 30fps)
// Panels slide in
export const PANEL_SLIDE_IN_START = 0;
export const PANEL_SLIDE_IN_END = 25;

// Divider fade in
export const DIVIDER_FADE_START = 15;
export const DIVIDER_FADE_END = 30;

// Left header + arrow
export const LEFT_HEADER_START = 25;
export const LEFT_HEADER_END = 45;

// Left stat counter + descriptor
export const LEFT_STAT_START = 35;
export const LEFT_STAT_END = 55;

// Right header + arrow
export const RIGHT_HEADER_START = 45;
export const RIGHT_HEADER_END = 65;

// Right stat counter + descriptor
export const RIGHT_STAT_START = 55;
export const RIGHT_STAT_END = 75;

// Source attribution
export const SOURCE_FADE_START = 70;
export const SOURCE_FADE_END = 90;

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
