// Part1Economics10DoubleMeterInsight constants
// "Double Meter Insight" — key insight beat with dual vertical meters

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const BG_COLOR = "#0D1117";

// Meter positions
export const LEFT_METER_X = 580;
export const RIGHT_METER_X = 1340;
export const METER_CENTER_Y = 480;

// Meter dimensions
export const METER_WIDTH = 60;
export const METER_HEIGHT = 400;
export const METER_RADIUS = 8;

// Colors
export const LEFT_COLOR = "#4A90D9"; // Effective Context Window
export const RIGHT_COLOR = "#5AAA6E"; // Model Performance
export const TRACK_FILL = "#1A2332";
export const TRACK_BORDER = "#334155";
export const SCALE_LABEL_COLOR = "#94A3B8";
export const TEXT_COLOR = "#E2E8F0";

// Typography
export const FONT_FAMILY = "Inter, sans-serif";
export const HANDWRITTEN_FONT = "Caveat, cursive";

// Total duration: 750 frames at 30fps (25s)
export const TOTAL_FRAMES = 750;

// Animation phases
export const STILLNESS_END = 45; // 0-1.5s dark screen

export const TRACK_FADE_START = 45; // 1.5s
export const TRACK_FADE_DURATION = 20;

export const SCALE_FADE_START = 75; // 2.5s
export const SCALE_FADE_DURATION = 20;

export const FILL_START = 105; // 3.5s
export const FILL_DURATION = 120; // 4s of filling

export const PEAK_PULSE_START = 225; // 7.5s
export const PEAK_PULSE_DURATION = 30;

export const CENTER_TEXT_START = 270; // 9s
export const CENTER_TEXT_STAGGER = 10; // gap between word groups
export const CENTER_TEXT_FADE = 15; // each group fade duration

export const SUMMARY_START = 330; // 11s
export const SUMMARY_FADE = 20;

export const ONGOING_PULSE_START = 390; // 13s
export const ONGOING_PULSE_CYCLE = 60; // frames per cycle

export const CHALLENGE_START = 480; // 16s
export const CHALLENGE_SLIDE_DURATION = 20;

// Left meter config
export const LEFT_SCALE_MARKERS = ["1×", "5×", "10×"];
export const LEFT_MAX_VALUE = 10;
export const LEFT_LABEL = "Effective Context Window";

// Right meter config
export const RIGHT_SCALE_MARKERS = ["baseline", "+50%", "+89%"];
export const RIGHT_MAX_VALUE = 89;
export const RIGHT_LABEL = "Model Performance";
