// Part2ParadigmShift10PromptMoldVisualization constants

// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 600;

// Backing panel
export const PANEL_X = 210;
export const PANEL_Y = 340;
export const PANEL_W = 1500;
export const PANEL_H = 400;
export const PANEL_BORDER_RADIUS = 16;
export const PANEL_BG = "rgba(15, 23, 42, 0.8)";
export const PANEL_BLUR = 10;

// Box dimensions
export const BOX_WIDTH = 240;
export const BOX_HEIGHT = 200;
export const BOX_BORDER_WIDTH = 3;
export const BOX_BORDER_RADIUS = 12;
export const ICON_SIZE = 64;

// Box 1 — PROMPT
export const PROMPT_CENTER_X = 420;
export const PROMPT_CENTER_Y = 490;
export const PROMPT_BORDER_COLOR = "#F97316";
export const PROMPT_FILL = "rgba(249,115,22,0.08)";
export const PROMPT_ICON_COLOR = "#FBBF24";
export const PROMPT_GLOW = "rgba(249,115,22,0.3)";

// Box 2 — CODE
export const CODE_CENTER_X = 960;
export const CODE_CENTER_Y = 490;
export const CODE_BORDER_COLOR = "#3B82F6";
export const CODE_FILL = "rgba(59,130,246,0.08)";
export const CODE_ICON_COLOR = "#60A5FA";
export const CODE_GLOW = "rgba(59,130,246,0.3)";

// Box 3 — TESTS
export const TESTS_CENTER_X = 1500;
export const TESTS_CENTER_Y = 490;
export const TESTS_BORDER_COLOR = "#22C55E";
export const TESTS_FILL = "rgba(34,197,94,0.08)";
export const TESTS_ICON_COLOR = "#4ADE80";
export const TESTS_GLOW = "rgba(34,197,94,0.3)";

// Arrows
export const ARROW_COLOR = "#94A3B8";
export const ARROW_STROKE_WIDTH = 2;
export const ARROWHEAD_SIZE = 12;

// Arrow 1: PROMPT → CODE
export const ARROW1_FROM_X = 540;
export const ARROW1_TO_X = 840;
export const ARROW1_Y = 490;

// Arrow 2: CODE ↔ TESTS
export const ARROW2_FROM_X = 1080;
export const ARROW2_TO_X = 1380;
export const ARROW2_Y = 490;

// Synthesis line
export const SYNTHESIS_Y = 700;
export const SYNTHESIS_DEFAULT_COLOR = "#94A3B8";
export const SYNTHESIS_HIGHLIGHT_COLOR = "#FFFFFF";

// Colors
export const BG_COLOR = "#0A1628";

// Animation timing (frames at 30fps)
export const PANEL_FADE_START = 0;
export const PANEL_FADE_END = 25;

export const BOX1_ENTER = 25;
export const BOX1_SETTLE = 55;

export const ARROW1_DRAW_START = 55;
export const ARROW1_DRAW_END = 75;

export const BOX2_ENTER = 75;
export const BOX2_SETTLE = 105;

export const ARROW2_DRAW_START = 105;
export const ARROW2_DRAW_END = 125;

export const BOX3_ENTER = 125;
export const BOX3_SETTLE = 155;

export const HOLD_START = 155;
export const HOLD_END = 200;

export const SYNTHESIS_APPEAR = 200;
export const SYNTHESIS_PHRASE1_HIGHLIGHT = 200;
export const SYNTHESIS_PHRASE2_HIGHLIGHT = 240;
export const SYNTHESIS_PHRASE3_HIGHLIGHT = 280;
export const SYNTHESIS_PHRASE_DURATION = 15;

export const FULL_DISPLAY_START = 320;
export const FULL_DISPLAY_END = 480;

export const FADEOUT_START = 480;
export const FADEOUT_END = 510;

// Glow pulse
export const GLOW_PULSE_SPEED = 0.084; // ~2.5s period at 30fps
export const GLOW_PULSE_MIN = 0.15;
export const GLOW_PULSE_MAX = 0.3;

// Spring config for box scale-in
export const SPRING_DAMPING = 14;
export const SPRING_STIFFNESS = 180;
