// ─── Canvas ────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 240;
export const FPS = 30;

// ─── Background ────────────────────────────────────────────────────
export const BG_COLOR = "#0D1117";

// ─── Divider ───────────────────────────────────────────────────────
export const DIVIDER_X = 960;
export const DIVIDER_WIDTH = 2;
export const DIVIDER_COLOR = "#334155";
export const DIVIDER_OPACITY = 0.4;

// ─── Panel regions ─────────────────────────────────────────────────
export const LEFT_PANEL_WIDTH = DIVIDER_X - 1; // 0..958
export const RIGHT_PANEL_X = DIVIDER_X + DIVIDER_WIDTH; // 962
export const RIGHT_PANEL_WIDTH = CANVAS_WIDTH - RIGHT_PANEL_X; // 958

// ─── Left panel styling ────────────────────────────────────────────
export const LEFT_TINT_COLOR = "#4A90D9";
export const LEFT_TINT_OPACITY = 0.02;
export const LEFT_VIGNETTE_COLOR = "#000000";
export const LEFT_VIGNETTE_OPACITY = 0.15;
export const LEFT_LABEL = "2025";
export const LEFT_LABEL_X = 24;
export const LEFT_LABEL_Y = 20;

// ─── Right panel styling ───────────────────────────────────────────
export const RIGHT_TINT_COLOR = "#D4A043";
export const RIGHT_TINT_OPACITY = 0.04;
export const RIGHT_VIGNETTE_COLOR = "#0A0500";
export const RIGHT_VIGNETTE_OPACITY = 0.2;
export const RIGHT_LABEL = "1955";
export const RIGHT_LABEL_X = 24; // relative to panel
export const RIGHT_LABEL_Y = 20;

// ─── Film grain ────────────────────────────────────────────────────
export const GRAIN_OPACITY = 0.06;
export const GRAIN_FPS = 12;

// ─── Animation timing (frames) ─────────────────────────────────────
export const FADE_IN_END = 15;
export const GLOW_START = 180;
export const GLOW_DURATION = 60;
export const GLOW_CYCLE_FRAMES = 30;

// ─── Divider glow colors ──────────────────────────────────────────
export const GLOW_COLOR_LEFT = "#4A90D9";
export const GLOW_COLOR_RIGHT = "#D9944A";
export const GLOW_OPACITY = 0.3;

// ─── Typography ────────────────────────────────────────────────────
export const LABEL_FONT_FAMILY = "Inter, sans-serif";
export const LABEL_FONT_SIZE = 16;
export const LABEL_FONT_WEIGHT = 600;
export const LABEL_COLOR = "#8B949E";
export const LABEL_OPACITY = 0.6;
