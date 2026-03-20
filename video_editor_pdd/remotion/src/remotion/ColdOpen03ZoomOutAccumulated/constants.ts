// === Colors ===
export const BG_LEFT = "#0D1117";
export const BG_RIGHT = "#1A1410";
export const DIVIDER_COLOR = "#334155";
export const DIVIDER_OPACITY = 0.4;
export const DIVIDER_WIDTH = 2;

// Left panel colors
export const CODE_BLOCK_FILL = "#161B22";
export const CODE_BLOCK_BORDER = "#30363D";
export const CODE_BLOCK_BORDER_OPACITY = 0.5;
export const DIFF_RED = "#F85149";
export const DIFF_GREEN = "#3FB950";
export const COMMENT_TEXT_COLOR = "#8B949E";
export const COMMENT_TEXT_OPACITY = 0.35;
export const RED_GLOW_COLOR = "#F85149";
export const RED_GLOW_OPACITY = 0.04;

// Right panel colors
export const DRAWER_WOOD_COLOR = "#8B6D4B";
export const STITCH_COLOR = "#D9944A";
export const GARMENT_COLORS = ["#F5F0E8", "#2A3A5C", "#7A7A7A", "#6B4F3A", "#D4C5A9"];

// Counter colors
export const LEFT_COUNTER_COLOR = "#F85149";
export const RIGHT_COUNTER_COLOR = "#D9944A";
export const COUNTER_OPACITY = 0.85;
export const SUFFIX_OPACITY = 0.6;

// === Dimensions ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const SPLIT_X = 960;
export const PANEL_WIDTH = 960;

// Code blocks
export const CODE_BLOCK_W = 40;
export const CODE_BLOCK_H = 24;
export const CODE_BLOCK_COUNT = 80;
export const DIFF_MARKER_PERCENT = 60;

// === Typography ===
export const FONT_FAMILY = "Inter, sans-serif";
export const COMMENT_FONT_SIZE = 11;
export const COUNTER_FONT_SIZE = 28;
export const SUFFIX_FONT_SIZE = 16;

// === Animation Timing ===
export const TOTAL_FRAMES = 210;
export const ZOOM_START = 10;
export const ZOOM_END = 90;
export const ZOOM_DURATION = 80;
export const ZOOM_FROM = 1.0;
export const ZOOM_TO = 0.15;
export const COMMENTS_START = 90;
export const COMMENTS_DURATION = 50;
export const COUNTER_START = 140;
export const COUNTER_DURATION = 40;
export const PULSE_START = 180;
export const PULSE_DURATION = 30;

// === Data ===
export const FLOATING_COMMENTS = [
  "// TODO: refactor",
  "// HACK",
  "// fixed null case",
  "// workaround for #412",
  "// legacy — do not touch",
  "// temporary fix 2023-04",
];

export const GARMENT_TYPES = ["sock", "shirt", "trouser", "sock", "sweater"];

export const LEFT_COUNTER_TARGET = 1247;
export const RIGHT_COUNTER_TARGET = 47;

// Seeded pseudo-random for deterministic layout
export function seededRandom(seed: number): number {
  const x = Math.sin(seed * 9301 + 49297) * 233280;
  return x - Math.floor(x);
}
