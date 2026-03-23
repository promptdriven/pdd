// ── Colors ──────────────────────────────────────────────
export const BG_COLOR = "#0D1117";
export const PDD_BLUE = "#4A90D9";
export const PDD_BLUE_GLOW = "rgba(74, 144, 217, 0.15)";
export const OVERLAY_BG = "rgba(13, 17, 23, 0.88)";

export const TERMINAL_BG = "#161B22";
export const TERMINAL_BORDER = "#30363D";
export const TERMINAL_PROMPT_COLOR = "#5AAA6E";
export const TERMINAL_CMD_COLOR = "#E2E8F0";
export const TERMINAL_STATS_COLOR = "#94A3B8";

export const CODE_TEXT_COLOR = "#E2E8F0";
export const CODE_KEYWORD_COLOR = "#C678DD";
export const CODE_STRING_COLOR = "#98C379";
export const CODE_FUNCTION_COLOR = "#61AFEF";
export const CODE_TYPE_COLOR = "#E5C07B";
export const CODE_COMMENT_COLOR = "#5C6370";
export const CODE_PARAM_COLOR = "#ABB2BF";

// ── Dimensions ──────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

export const TITLE_X = 960;
export const TITLE_Y = 490;
export const TITLE_FONT_SIZE = 56;
export const TITLE_LETTER_SPACING = 1;

export const RULE_Y = 545;
export const RULE_WIDTH = 160;
export const RULE_HEIGHT = 2;

export const TERMINAL_X = 1540;
export const TERMINAL_Y = 980;
export const TERMINAL_WIDTH = 360;
export const TERMINAL_HEIGHT = 80;
export const TERMINAL_BORDER_RADIUS = 8;

// ── Animation Timing (frames) ───────────────────────────
export const TOTAL_FRAMES = 75;

// Phase 1: Code dims (0–10)
export const CODE_DIM_START = 0;
export const CODE_DIM_END = 10;

// Phase 2: Title fade-in + slide (10–30)
export const TITLE_FADE_START = 10;
export const TITLE_FADE_END = 30;

// Phase 2b: Glow bloom (10–35)
export const GLOW_BLOOM_START = 10;
export const GLOW_BLOOM_END = 35;

// Phase 3: Rule draw (35–45)
export const RULE_DRAW_START = 35;
export const RULE_DRAW_END = 45;

// Terminal opacity reduce (0–15)
export const TERMINAL_FADE_START = 0;
export const TERMINAL_FADE_END = 15;
export const TERMINAL_OPACITY_FROM = 0.92;
export const TERMINAL_OPACITY_TO = 0.5;

// ── Opacity values ──────────────────────────────────────
export const CODE_UNDERLAY_OPACITY = 0.12;
export const TITLE_OPACITY = 0.95;
export const RULE_OPACITY = 0.7;
export const TITLE_SLIDE_DISTANCE = 12;
