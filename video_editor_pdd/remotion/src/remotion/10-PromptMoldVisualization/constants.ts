// Part2ParadigmShift10PromptMoldVisualization constants

// Canvas
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const TOTAL_FRAMES = 600;

// Background
export const BG_COLOR = "#0A1628";

// Equation region
export const PANEL_X = 210;
export const PANEL_Y = 340;
export const PANEL_W = 1500;
export const PANEL_H = 400;
export const PANEL_RADIUS = 16;
export const PANEL_BG = "rgba(15, 23, 42, 0.8)";

// Box dimensions
export const BOX_W = 240;
export const BOX_H = 200;
export const BOX_RADIUS = 12;
export const BOX_BORDER_WIDTH = 3;
export const ICON_SIZE = 64;

// Box positions (center coordinates)
export const BOX1_X = 420;
export const BOX2_X = 960;
export const BOX3_X = 1500;
export const BOX_Y = 490;

// Box colors — PROMPT
export const PROMPT_BORDER = "#F97316";
export const PROMPT_FILL = "rgba(249, 115, 22, 0.08)";
export const PROMPT_ICON = "#FBBF24";
export const PROMPT_GLOW = "rgba(249, 115, 22, 0.3)";

// Box colors — CODE
export const CODE_BORDER = "#3B82F6";
export const CODE_FILL = "rgba(59, 130, 246, 0.08)";
export const CODE_ICON = "#60A5FA";
export const CODE_GLOW = "rgba(59, 130, 246, 0.3)";

// Box colors — TESTS
export const TESTS_BORDER = "#22C55E";
export const TESTS_FILL = "rgba(34, 197, 94, 0.08)";
export const TESTS_ICON = "#4ADE80";
export const TESTS_GLOW = "rgba(34, 197, 94, 0.3)";

// Arrow
export const ARROW_COLOR = "#94A3B8";
export const ARROW_STROKE = 2;
export const ARROWHEAD_SIZE = 12;

// Arrow positions
export const ARROW1_X1 = 540;
export const ARROW1_X2 = 840;
export const ARROW2_X1 = 1080;
export const ARROW2_X2 = 1380;
export const ARROW_Y = 490;

// Synthesis line
export const SYNTHESIS_Y = 700;
export const SYNTHESIS_DEFAULT_COLOR = "#94A3B8";
export const SYNTHESIS_HIGHLIGHT_COLOR = "#FFFFFF";

// Typography
export const FONT_FAMILY = "Inter, sans-serif";
export const LABEL_FONT_SIZE = 24;
export const LABEL_LETTER_SPACING = "0.1em";
export const SUBTITLE_FONT_SIZE = 18;
export const ARROW_LABEL_FONT_SIZE = 14;
export const SYNTHESIS_FONT_SIZE = 22;

// Animation frames
export const PANEL_FADE_START = 0;
export const PANEL_FADE_END = 25;

export const BOX1_ENTER = 25;
export const BOX1_ENTER_END = 55;

export const ARROW1_START = 55;
export const ARROW1_END = 75;

export const BOX2_ENTER = 75;
export const BOX2_ENTER_END = 105;

export const ARROW2_START = 105;
export const ARROW2_END = 125;

export const BOX3_ENTER = 125;
export const BOX3_ENTER_END = 155;

export const HOLD_START = 155;
export const HOLD_END = 200;

export const SYNTH_ENTER = 200;
export const SYNTH_PHRASE1_START = 200;
export const SYNTH_PHRASE1_END = 240;
export const SYNTH_PHRASE2_START = 240;
export const SYNTH_PHRASE2_END = 280;
export const SYNTH_PHRASE3_START = 280;
export const SYNTH_PHRASE3_END = 320;

export const FINAL_HOLD_START = 320;
export const FINAL_HOLD_END = 480;

export const FADEOUT_START = 480;
export const FADEOUT_END = 510;

// Glow pulse: sinusoidal, 2.5s period = 75 frames at 30fps
export const GLOW_PERIOD_FRAMES = 75;
export const GLOW_ANGULAR_VELOCITY = (2 * Math.PI) / GLOW_PERIOD_FRAMES;
