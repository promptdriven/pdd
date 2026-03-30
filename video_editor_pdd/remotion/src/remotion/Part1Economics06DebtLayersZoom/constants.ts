// Part1Economics06DebtLayersZoom — constants
// Duration: ~18s (540 frames @ 30fps)

export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 540;

// Background
export const BG_COLOR = "#0A0F1A";

// Layer colors
export const CODE_COMPLEXITY_COLOR = "#D9944A";
export const CONTEXT_ROT_COLOR = "#F59E0B";
export const NOISE_COLOR = "#FFFFFF";

// Layer opacities
export const CODE_COMPLEXITY_OPACITY = 0.18;
export const CONTEXT_ROT_OPACITY = 0.12;
export const NOISE_OPACITY = 0.03;
export const NOISE_GRAIN_SIZE = 2;

// Pre-zoom debt area (monolithic amber)
export const DEBT_AREA_COLOR = "#D9944A";
export const DEBT_AREA_OPACITY = 0.12;

// Zoom configuration
export const ZOOM_ORIGIN_X = 1200;
export const ZOOM_ORIGIN_Y = 400;
export const ZOOM_FACTOR = 3.0;

// Animation timing (frames)
export const ZOOM_START = 0;
export const ZOOM_END = 90;
export const SPLIT_START = 90;
export const SPLIT_END = 180;
export const LABEL_FADE_START = 180;
export const LABEL_FADE_END = 200; // 20 frames fade
export const HOLD_START = 270;

// Layer geometry (post-zoom, in zoomed coordinate space)
export const LAYER_GAP = 4;
export const DEBT_AREA_TOP = 260;
export const DEBT_AREA_BOTTOM = 680;
export const DEBT_AREA_LEFT = 200;
export const DEBT_AREA_RIGHT = 1720;

// The midpoint where layers split — upper layer is slightly taller
export const SPLIT_Y = 440; // upper layer: 260-440 (180px), lower: 444-680 (236px)

// Label typography
export const LABEL_FONT_SIZE = 16;
export const LABEL_FONT_WEIGHT = 700;
export const LABEL_FONT_FAMILY = "Inter, sans-serif";

// Noise animation
export const NOISE_DRIFT_PX_PER_FRAME = 0.5;

// Chart reference lines (subtle grid for context during zoom)
export const GRID_COLOR = "#FFFFFF";
export const GRID_OPACITY = 0.06;
export const YEAR_LABELS = ["2022", "2023", "2024", "2025", "2026"];
