// ── Layout ──────────────────────────────────────────────────────
export const CANVAS_W = 1920;
export const CANVAS_H = 1080;
export const SPLIT_X = 960;
export const SPLIT_LINE_W = 2;
export const LEFT_PANEL_W = SPLIT_X - 1; // 0..958
export const RIGHT_PANEL_X = SPLIT_X + 2; // 962..1920
export const RIGHT_PANEL_W = CANVAS_W - RIGHT_PANEL_X; // 958

// ── Duration ────────────────────────────────────────────────────
export const TOTAL_FRAMES = 360;

// ── Colors ──────────────────────────────────────────────────────
export const BG_COLOR = "#000000";
export const SPLIT_LINE_COLOR = "#334155";
export const SPLIT_LINE_OPACITY = 0.2;

export const LEFT_GRADE_COLOR = "#D4A043";
export const LEFT_GRADE_OPACITY = 0.04;
export const LEFT_HEADER_COLOR = "#D9944A";
export const LEFT_VIGNETTE_EDGE = "#0A0500";

export const RIGHT_GRADE_COLOR = "#4A90D9";
export const RIGHT_GRADE_OPACITY = 0.03;
export const RIGHT_HEADER_COLOR = "#4A90D9";
export const RIGHT_VIGNETTE_EDGE = "#000510";

export const CAPTION_COLOR = "#E2E8F0";
export const CAPTION_OPACITY = 0.6;

export const FLASH_COLOR = "#FFFFFF";
export const FLASH_PEAK_OPACITY = 0.03;
export const GLOW_LINE_COLOR = "#E2E8F0";
export const GLOW_LINE_PEAK_OPACITY = 0.15;

// ── Typography ──────────────────────────────────────────────────
export const HEADER_FONT_SIZE = 14;
export const HEADER_FONT_WEIGHT = 600;
export const HEADER_LETTER_SPACING = 2;
export const HEADER_OPACITY = 0.4;
export const HEADER_Y = 40;

export const CAPTION_FONT_SIZE = 13;
export const CAPTION_Y = 920;

// ── Animation timing (frames) ───────────────────────────────────
export const SPLIT_LINE_DRAW_START = 0;
export const SPLIT_LINE_DRAW_DUR = 15;

export const HEADER_FADE_START = 5;
export const HEADER_FADE_DUR = 15;

export const REALIZATION_FLASH_START = 180;
export const REALIZATION_FLASH_RAMP_UP = 10;
export const REALIZATION_FLASH_RAMP_DOWN = 10;

export const CAPTION_FADE_START = 200;
export const CAPTION_FADE_DUR = 20;

export const ICON_APPEAR_START = 260;
export const ICON_APPEAR_DUR = 15;

// ── Icon positions ──────────────────────────────────────────────
export const LEFT_ICON_X = 200;
export const LEFT_ICON_Y = 900;
export const RIGHT_ICON_X = 1680 - RIGHT_PANEL_X; // relative inside panel
export const RIGHT_ICON_Y = 900;
