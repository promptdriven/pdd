// === Canvas ===
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 330;

// === Background & Grid ===
export const BG_COLOR = "#0A0F1A";
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.06;

// === Chart Layout ===
export const CHART_LEFT = 120;
export const CHART_RIGHT = 1800;
export const CHART_TOP = 100;
export const CHART_BOTTOM = 800;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// === Chart Colors ===
export const AXIS_COLOR = "#475569";
export const IDEAL_LINE_COLOR = "#22C55E";
export const ACTUAL_LINE_COLOR = "#EF4444";
export const DEBT_FILL_START = "rgba(239, 68, 68, 0.08)";
export const DEBT_FILL_END = "rgba(239, 68, 68, 0.25)";
export const CONTEXT_ROT_COLOR = "#EF4444";

// === Feedback Loop Nodes ===
export const NODE_PATCHING = {
  text: "Faster patching",
  color: "#4A90D9",
  x: 960,
  y: 350,
};
export const NODE_GROWTH = {
  text: "Faster growth",
  color: "#D9944A",
  x: 1100,
  y: 550,
};
export const NODE_ROT = {
  text: "Faster rot",
  color: "#EF4444",
  x: 820,
  y: 550,
};

// === Feedback Loop Arrow ===
export const ARROW_COLOR = "#E2E8F0";
export const ARROW_OPACITY = 0.5;
export const ARROW_PULSE_COLOR = "#FFFFFF";
export const ARROW_PULSE_OPACITY = 0.8;
export const ARROW_THICKNESS = 2;

// === Feedback Loop Timing ===
export const LOOP_BUILD_START = 60;
export const NODE_APPEAR_DURATION = 20;
export const ARROW_DRAW_DURATION = 25;
export const LOOP_BUILD_SEGMENT = 30; // frames between each node/arrow pair
export const PULSE_CYCLE_FRAMES = 90;
export const LOOP_CYCLE_START = 150;
export const HOLD_START = 270;

// === Typography ===
export const NODE_FONT_SIZE = 16;
export const NODE_FONT_WEIGHT = 600;
export const NODE_FONT_FAMILY = "Inter, sans-serif";

// === Label Overlay ===
export const LABEL_BG_COLOR = "rgba(10, 15, 26, 0.75)";
export const LABEL_PADDING_X = 14;
export const LABEL_PADDING_Y = 8;
export const LABEL_BORDER_RADIUS = 6;

// === Noise Texture ===
export const NOISE_BASE_OPACITY = 0.12;
export const NOISE_PULSE_AMPLITUDE = 0.15;
