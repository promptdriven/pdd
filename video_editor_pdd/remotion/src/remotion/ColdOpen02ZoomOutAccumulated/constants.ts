// ── Layout ──
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 210;

export const SPLIT_X = 960;
export const LEFT_PANEL_WIDTH = 958;
export const RIGHT_PANEL_WIDTH = 958;
export const DIVIDER_WIDTH = 2;

// ── Colors ──
export const BG_COLOR = "#000000";
export const DIVIDER_COLOR = "#334155";
export const DIVIDER_OPACITY = 0.12;

// Left panel (code)
export const CODE_TILE_BG = "#0F172A";
export const DIFF_GREEN = "#22C55E";
export const DIFF_RED = "#EF4444";
export const TODO_RED = "#EF4444";
export const COMMENT_GRAY = "#64748B";
export const COUNTER_BLUE = "#4A90D9";
export const CODE_TEXT_SLATE = "#94A3B8";
export const CODE_KEYWORD_PURPLE = "#A78BFA";
export const CODE_STRING_GREEN = "#86EFAC";

// Right panel (garments)
export const STITCH_AMBER = "#D9944A";
export const DRAWER_BG = "#3E2A1A";
export const GARMENT_BASE = "#8B7355";
export const GARMENT_SOCK = "#6B5B4A";
export const GARMENT_SHIRT = "#7A6650";
export const GARMENT_TROUSER = "#5C4D3C";

// ── Grid config ──
export const GRID_ROWS = 8;
export const GRID_COLS = 8;
export const TILE_WIDTH = 110;
export const TILE_HEIGHT = 90;
export const TILE_PADDING = 10;
export const TILE_GAP = 6;

// ── Zoom config ──
export const ZOOM_START_SCALE = 1.0;
export const ZOOM_END_SCALE = 0.15;
export const ZOOM_START_FRAME = 15;
export const ZOOM_DURATION = 105; // frames 15-120

// ── Counter config ──
export const COUNTER_START_FRAME = 120;
export const COUNTER_DURATION = 60; // frames 120-180
export const PATCHES_FINAL = 1247;
export const MENDED_FINAL = 47;

// ── Inline comments ──
export const INLINE_COMMENTS = [
  "// fixed null case",
  "// workaround for #412",
  "// TODO: refactor",
  "// temporary fix (2019)",
  "// don't touch this",
  "// legacy",
  "// FIXME",
  "// hack for edge case",
  "// see issue #891",
  "// deprecated",
  "// patch v2.3.1",
  "// compat shim",
] as const;

// ── Garment types ──
export const GARMENT_TYPES = ["sock", "shirt", "trouser"] as const;
