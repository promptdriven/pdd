// constants.ts — Part1Economics06DebtLayersZoom
// Colors, dimensions, and animation timing

// === Canvas ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = "#0A0F1A";

// === Duration ===
export const TOTAL_FRAMES = 540;
export const FPS = 30;

// === Animation Phases (frames) ===
export const ZOOM_START = 0;
export const ZOOM_END = 90;
export const SPLIT_START = 90;
export const SPLIT_END = 180;
export const LABEL_FADE_START = 180;
export const LABEL_FADE_END = 200; // 20 frames for label fade
export const HOLD_START = 270;

// === Zoom ===
export const ZOOM_ORIGIN_X = 1200;
export const ZOOM_ORIGIN_Y = 400;
export const ZOOM_SCALE_FROM = 1.0;
export const ZOOM_SCALE_TO = 3.0;

// === Layer Colors ===
export const CODE_COMPLEXITY_COLOR = "#D9944A";
export const CODE_COMPLEXITY_FILL_OPACITY = 0.18;
export const CONTEXT_ROT_COLOR = "#F59E0B";
export const CONTEXT_ROT_FILL_OPACITY = 0.12;

// === Pre-zoom debt area ===
export const DEBT_AREA_COLOR = "#D9944A";
export const DEBT_AREA_OPACITY = 0.12;

// === Noise Texture ===
export const NOISE_COLOR = "#FFFFFF";
export const NOISE_OPACITY = 0.03;
export const NOISE_GRAIN_SIZE = 2;
export const NOISE_DRIFT_PX_PER_FRAME = 0.5;

// === Layer Layout (within zoomed view) ===
export const LAYER_GAP = 4; // hairline gap between layers in px
export const LAYER_AREA_TOP = 200; // top of the combined debt area
export const LAYER_AREA_BOTTOM = 700; // bottom of the combined debt area
export const LAYER_AREA_LEFT = 400;
export const LAYER_AREA_RIGHT = 1520;

// Derived: upper layer is slightly taller (growing faster)
export const LAYER_MIDPOINT_RATIO = 0.45; // lower layer gets 45%, upper gets 55%

// === Typography ===
export const LABEL_FONT_SIZE = 16;
export const LABEL_FONT_WEIGHT = 700;
export const LABEL_FONT_FAMILY = "Inter, sans-serif";
export const LABEL_MIN_OPACITY = 0.78;

// === Chart Reference Lines (simplified representation of the cost chart) ===
export const CHART_LINE_COLOR = "#3B82F6";
export const CHART_GRID_COLOR = "#FFFFFF";
export const CHART_GRID_OPACITY = 0.08;
export const CHART_AXIS_COLOR = "#FFFFFF";
export const CHART_AXIS_OPACITY = 0.3;

// === Year range for the zoomed-in area ===
export const YEAR_LABELS = ["2022", "2023", "2024", "2025", "2026"];
