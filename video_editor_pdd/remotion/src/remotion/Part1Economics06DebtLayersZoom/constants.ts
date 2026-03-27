// === Colors ===
export const BG_COLOR = "#0A0F1A";

// Layer colors
export const CODE_COMPLEXITY_COLOR = "#D9944A";
export const CONTEXT_ROT_COLOR = "#F59E0B";

// Pre-zoom unified debt color
export const UNIFIED_DEBT_COLOR = "#D9944A";
export const UNIFIED_DEBT_OPACITY = 0.12;

// Layer fill opacities
export const CODE_COMPLEXITY_OPACITY = 0.18;
export const CONTEXT_ROT_OPACITY = 0.12;

// Noise overlay
export const NOISE_COLOR = "#FFFFFF";
export const NOISE_OPACITY = 0.03;
export const NOISE_GRAIN_SIZE = 2;
export const NOISE_DRIFT_PX_PER_FRAME = 0.5;

// Labels
export const LABEL_FONT_SIZE = 16;
export const LABEL_FONT_WEIGHT = 700;
export const LABEL_FONT_FAMILY = "Inter, sans-serif";
export const LABEL_PRIMARY_OPACITY = 0.9;

// Axis / chart reference colors
export const AXIS_COLOR = "#FFFFFF";
export const AXIS_OPACITY = 0.15;
export const GRID_LINE_OPACITY = 0.08;

// === Dimensions ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// Chart area (the debt region we zoom into)
export const CHART_LEFT = 200;
export const CHART_RIGHT = 1720;
export const CHART_TOP = 120;
export const CHART_BOTTOM = 900;
export const CHART_WIDTH = CHART_RIGHT - CHART_LEFT;
export const CHART_HEIGHT = CHART_BOTTOM - CHART_TOP;

// Debt area shape (approximate trapezoid of the debt region from the cost chart)
// This represents the shaded area between generate and patch cost curves (2018-2026)
export const DEBT_AREA_X = 600;
export const DEBT_AREA_WIDTH = 1100;
export const DEBT_AREA_Y_TOP = 280;
export const DEBT_AREA_Y_BOTTOM = 680;

// Zoom target (right portion, 2022-2026 range)
export const ZOOM_ORIGIN_X = 1200;
export const ZOOM_ORIGIN_Y = 400;
export const ZOOM_FACTOR = 3.0;

// Layer separation
export const LAYER_GAP = 4;

// Post-zoom layer regions (as they appear after zoom fills the frame)
export const LOWER_LAYER_TOP = 520;
export const LOWER_LAYER_HEIGHT = 280;
export const UPPER_LAYER_TOP = 180;
export const UPPER_LAYER_HEIGHT = 320; // slightly taller — growing faster

// === Timing (frames @ 30fps) ===
export const FPS = 30;
export const TOTAL_DURATION = 540;

// Phase 1: Camera zoom (0-3s)
export const ZOOM_START = 0;
export const ZOOM_END = 90;

// Phase 2: Layer separation (3-6s)
export const SPLIT_START = 90;
export const SPLIT_END = 180;

// Phase 3: Labels + texture (6-9s)
export const LABEL_START = 180;
export const LABEL_FADE_DURATION = 20;
export const TEXTURE_START = 180;
export const TEXTURE_FADE_DURATION = 30;

// Phase 4: Hold with noise animation (9-18s)
export const HOLD_START = 270;
export const HOLD_END = 540;

// Year labels for the chart backdrop
export const YEAR_LABELS = ["2018", "2019", "2020", "2021", "2022", "2023", "2024", "2025", "2026"];
