// ─── Layout ───────────────────────────────────────────────────────────────────
export const COMP_WIDTH = 1920;
export const COMP_HEIGHT = 1080;
export const DURATION_FRAMES = 240;
export const FPS = 30;

// ─── Split Divider ────────────────────────────────────────────────────────────
export const DIVIDER_X = 960;
export const DIVIDER_WIDTH = 2;
export const DIVIDER_COLOR = '#334155';
export const DIVIDER_OPACITY = 0.4;

// ─── Panel Regions ────────────────────────────────────────────────────────────
export const LEFT_PANEL_WIDTH = DIVIDER_X - DIVIDER_WIDTH / 2; // 959
export const RIGHT_PANEL_LEFT = DIVIDER_X + DIVIDER_WIDTH / 2; // 961
export const RIGHT_PANEL_WIDTH = COMP_WIDTH - RIGHT_PANEL_LEFT; // 959

// ─── Background ───────────────────────────────────────────────────────────────
export const BG_COLOR = '#0D1117';

// ─── Left Panel (Developer / 2025) ───────────────────────────────────────────
export const LEFT_TINT_COLOR = '#4A90D9';
export const LEFT_TINT_OPACITY = 0.02;
export const LEFT_VIGNETTE_COLOR = '#000000';
export const LEFT_VIGNETTE_OPACITY = 0.15;
export const LEFT_LABEL = '2025';
export const LEFT_LABEL_X = 24;
export const LEFT_LABEL_Y = 20;

// ─── Right Panel (Grandmother / 1955) ────────────────────────────────────────
export const RIGHT_TINT_COLOR = '#D4A043';
export const RIGHT_TINT_OPACITY = 0.04;
export const RIGHT_VIGNETTE_COLOR = '#0A0500';
export const RIGHT_VIGNETTE_OPACITY = 0.2;
export const RIGHT_LABEL = '1955';
export const RIGHT_LABEL_X = 25; // relative to panel (986 absolute - 961 panel left)
export const RIGHT_LABEL_Y = 20;

// ─── Film Grain ───────────────────────────────────────────────────────────────
export const FILM_GRAIN_OPACITY = 0.06;
export const FILM_GRAIN_FPS = 12;

// ─── Typography ───────────────────────────────────────────────────────────────
export const HEADER_FONT_FAMILY = 'Inter, sans-serif';
export const HEADER_FONT_SIZE = 16;
export const HEADER_FONT_WEIGHT = 600;
export const HEADER_TEXT_COLOR = '#8B949E';
export const HEADER_TEXT_OPACITY = 0.6;

// ─── Animation Timing ─────────────────────────────────────────────────────────
export const FADE_IN_END = 15;
export const GLOW_START = 180;
export const GLOW_DURATION = 60;
export const GLOW_CYCLE_FRAMES = 30;

// ─── Divider Glow ─────────────────────────────────────────────────────────────
export const GLOW_COLOR_LEFT = '#4A90D9';
export const GLOW_COLOR_RIGHT = '#D9944A';
export const GLOW_MAX_OPACITY = 0.3;
