// ── Animation timing (frames at 30fps, relative to component start) ──
export const TOTAL_FRAMES = 90;

// Phase 1: Panels + split line fade in (frames 0-20)
export const PANEL_FADE_START = 0;
export const PANEL_FADE_END = 20;

// Phase 2: Question text fade in + drift (frames 20-40)
export const QUESTION_FADE_START = 20;
export const QUESTION_FADE_END = 40;
export const QUESTION_DRIFT_Y = 20; // pixels upward

// Phase 3: Labels fade in (frames 40-50)
export const LABEL_FADE_START = 40;
export const LABEL_FADE_END = 50;

// Phase 4: Fade out (frames 60-90)
export const FADE_OUT_START = 60;
export const FADE_OUT_END = 90;

// ── Layout ──────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const SPLIT_X = 960;
export const SPLIT_LINE_WIDTH = 2;

// Question text position
export const QUESTION_CENTER_Y = 480;

// Label positions
export const LEFT_LABEL_X = 40;
export const LEFT_LABEL_Y = 1040;
export const RIGHT_LABEL_X = 1880;
export const RIGHT_LABEL_Y = 1040;

// Code texture: horizontal lines
export const CODE_LINE_INTERVAL = 8; // px between lines
export const CODE_LINE_COUNT = Math.floor(CANVAS_HEIGHT / CODE_LINE_INTERVAL);

// ── Colors ──────────────────────────────────────────────────────────
export const BG_COLOR = "#0A1628";
export const LEFT_PANEL_BG = "rgba(15, 23, 42, 0.6)";
export const RIGHT_PANEL_BG = "rgba(15, 23, 42, 0.3)";
export const SPLIT_LINE_COLOR = "rgba(255, 255, 255, 0.2)";
export const CODE_LINE_COLOR = "rgba(255, 255, 255, 0.04)";
export const RADIAL_GLOW_COLOR = "#3B82F6";
export const RADIAL_GLOW_OPACITY = 0.05;

// Left label
export const LEFT_LABEL_COLOR = "rgba(255, 255, 255, 0.3)";
export const LEFT_LABEL_MAX_OPACITY = 0.3;

// Right label
export const RIGHT_LABEL_COLOR = "rgba(59, 130, 246, 0.4)";
export const RIGHT_LABEL_MAX_OPACITY = 0.4;

// ── Typography ──────────────────────────────────────────────────────
export const QUESTION_FONT_SIZE = 48;
export const QUESTION_FONT_WEIGHT = 700;
export const QUESTION_LETTER_SPACING = "-0.01em";
export const QUESTION_COLOR = "#FFFFFF";
export const QUESTION_TEXT_SHADOW = "0 2px 20px rgba(0, 0, 0, 0.7)";

export const LABEL_FONT_SIZE = 18;
export const LABEL_FONT_WEIGHT = 400;

// ── Content ─────────────────────────────────────────────────────────
export const QUESTION_TEXT = "Why are we still patching?";
export const LEFT_LABEL_TEXT = "patching";
export const RIGHT_LABEL_TEXT = "building";
