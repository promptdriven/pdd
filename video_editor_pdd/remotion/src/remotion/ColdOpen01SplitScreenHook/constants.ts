// ── Canvas ────────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 240; // 8s at 30fps

// ── Split Layout ──────────────────────────────────────────────────────
export const SPLIT_X = 960;
export const LEFT_PANEL_WIDTH = 958; // 0 to 958
export const RIGHT_PANEL_X = 962; // 962 to 1920
export const RIGHT_PANEL_WIDTH = 958;
export const SPLIT_LINE_WIDTH = 2;

// ── Colors ────────────────────────────────────────────────────────────
export const BG_COLOR = "#000000";
export const SPLIT_LINE_COLOR = "#334155";
export const SPLIT_LINE_OPACITY = 0.12;

// Left panel — cool blue
export const LEFT_COLOR_GRADE = "#4A90D9";
export const LEFT_COLOR_GRADE_OPACITY = 0.02;
export const LEFT_VIGNETTE_COLOR = "#000510";
export const LEFT_VIGNETTE_OPACITY = 0.2;
export const LEFT_LABEL_COLOR = "#4A90D9";

// Right panel — warm amber
export const RIGHT_COLOR_GRADE = "#D4A043";
export const RIGHT_COLOR_GRADE_OPACITY = 0.04;
export const RIGHT_VIGNETTE_COLOR = "#0A0500";
export const RIGHT_VIGNETTE_OPACITY = 0.2;
export const RIGHT_LABEL_COLOR = "#D9944A";

// ── Typography ────────────────────────────────────────────────────────
export const LABEL_FONT_SIZE = 11;
export const LABEL_FONT_WEIGHT = 600;
export const LABEL_LETTER_SPACING = 3;
export const LABEL_Y = 36;
export const LABEL_BASE_OPACITY = 0.25;

// ── Animation Timing (frames at 30fps) ───────────────────────────────
// Phase 1: Hard cut reveal (0-10)
export const REVEAL_END = 10;

// Phase 2: Both subjects work (10-90)
// Phase 3: Both complete tasks (90-150)
// Phase 4: Hold — satisfaction (150-210)

// Phase 5: Year label pulse (210-240)
export const PULSE_START = 210;
export const PULSE_DURATION = 30;
export const PULSE_MIN_OPACITY = 0.25;
export const PULSE_MAX_OPACITY = 0.35;

// ── Content ──────────────────────────────────────────────────────────
export const LEFT_LABEL_TEXT = "2025";
export const RIGHT_LABEL_TEXT = "1955";
