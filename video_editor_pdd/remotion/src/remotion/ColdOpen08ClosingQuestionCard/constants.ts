// ColdOpen08ClosingQuestionCard constants

// Animation timing (frames at 30fps, local to this component)
// Spec: entry at frame 380 global → frame 0 local
export const PANEL_FADE_START = 0;
export const PANEL_FADE_END = 20; // 380→400 global
export const QUESTION_FADE_START = 20;
export const QUESTION_FADE_END = 40; // 400→420 global
export const LABEL_FADE_START = 40;
export const LABEL_FADE_END = 50; // 420→430 global (10 frames)
export const FADE_OUT_START = 60;
export const FADE_OUT_END = 90; // 440→470 global
export const TOTAL_FRAMES = 90;

// Layout
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const SPLIT_X = 960;
export const SPLIT_LINE_WIDTH = 2;

// Colors
export const BG_COLOR = "#0A1628";
export const LEFT_PANEL_COLOR = "rgba(15, 23, 42, 0.6)";
export const RIGHT_PANEL_COLOR = "rgba(15, 23, 42, 0.3)";
export const SPLIT_LINE_COLOR = "rgba(255, 255, 255, 0.2)";
export const GLOW_COLOR = "#3B82F6";

// Typography — Question
export const QUESTION_TEXT = "Why are we still patching?";
export const QUESTION_FONT_SIZE = 48;
export const QUESTION_COLOR = "#FFFFFF";
export const QUESTION_SHADOW = "0 2px 20px rgba(0, 0, 0, 0.7)";
export const QUESTION_LETTER_SPACING = "-0.01em";
export const QUESTION_Y = 480;
export const QUESTION_DRIFT = 20; // drift from 500→480

// Typography — Labels
export const LABEL_FONT_SIZE = 18;
export const LEFT_LABEL = "patching";
export const RIGHT_LABEL = "building";
export const LEFT_LABEL_COLOR = "rgba(255, 255, 255, 0.3)";
export const RIGHT_LABEL_COLOR = "rgba(59, 130, 246, 0.4)";
export const LABEL_PADDING_X = 40;
export const LABEL_BOTTOM_Y = 1040;

// Code texture
export const CODE_LINE_INTERVAL = 8;
export const CODE_LINE_COLOR = "rgba(255, 255, 255, 0.04)";

// Minimum opacity at frame 0 so content is visible immediately
export const MIN_INITIAL_OPACITY = 0.15;
