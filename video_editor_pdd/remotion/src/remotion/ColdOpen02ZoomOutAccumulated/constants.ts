// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BG_COLOR = "#0A1628";
export const FPS = 30;
export const TOTAL_FRAMES = 210;

// Split layout
export const SPLIT_X = 960;
export const DIVIDER_WIDTH = 2;
export const DIVIDER_COLOR = "#334155";
export const DIVIDER_OPACITY = 0.12;
export const LEFT_PANEL_WIDTH = 958;
export const RIGHT_PANEL_WIDTH = 958;
export const RIGHT_PANEL_X = 962;

// Zoom configuration
export const ZOOM_START_FRAME = 15;
export const ZOOM_DURATION = 105; // frames 15–120
export const ZOOM_END_FRAME = ZOOM_START_FRAME + ZOOM_DURATION; // 120
export const ZOOM_START_SCALE = 1.0;
export const ZOOM_END_SCALE = 0.15;

// Code tile grid (left panel)
export const GRID_ROWS = 8;
export const GRID_COLS = 8;
export const TILE_WIDTH = 110;
export const TILE_HEIGHT = 90;
export const TILE_GAP = 6;
export const TILE_PADDING = 10;
export const TILE_BG = "#0F172A";
export const TILE_BORDER_RADIUS = 4;
export const DIFF_MARKER_WIDTH = 4;
export const DIFF_GREEN = "#22C55E";
export const DIFF_RED = "#EF4444";
export const DIFF_MARKER_PERCENT = 0.6;
export const TILE_STAGGER_FRAMES = 3;

// TODO labels
export const TODO_COLOR = "#EF4444";
export const TODO_OPACITY = 0.5;
export const TODO_FONT_SIZE = 8;

// Inline comments
export const COMMENT_COLOR = "#64748B";
export const COMMENT_OPACITY = 0.3;
export const COMMENT_FONT_SIZE = 7;

// Code syntax colors
export const SYNTAX_KEYWORD = "#C084FC"; // purple
export const SYNTAX_STRING = "#34D399"; // green
export const SYNTAX_FUNCTION = "#60A5FA"; // blue
export const SYNTAX_OPERATOR = "#94A3B8"; // slate

// Counters
export const COUNTER_START_FRAME = 120;
export const COUNTER_DURATION = 60; // frames 120–180

export const PATCH_COUNTER_X = 40;
export const PATCH_COUNTER_Y = 1020;
export const PATCH_COUNTER_COLOR = "#4A90D9";
export const PATCH_COUNTER_OPACITY = 0.6;
export const PATCH_COUNTER_FINAL = 1247;

export const MENDED_COUNTER_X = 918; // relative to right panel (958 - 40)
export const MENDED_COUNTER_Y = 1020;
export const MENDED_COUNTER_COLOR = "#D9944A";
export const MENDED_COUNTER_OPACITY = 0.6;
export const MENDED_COUNTER_FINAL = 47;

export const COUNTER_FONT_SIZE = 14;

// Right panel — mended garments
export const DRAWER_BG = "#3D2B1F";
export const DRAWER_BORDER = "#5C4033";
export const GARMENT_STAGGER_FRAMES = 5;
export const STITCH_COLOR = "#D9944A";
export const STITCH_OPACITY = 0.3;

// Garment colors (warm tones)
export const GARMENT_COLORS = [
  "#8B6F5E", "#A67B5B", "#7B6B5A", "#9C8570",
  "#6B5B4F", "#B08968", "#8C7A6B", "#957A63",
  "#7A6655", "#A38B7A", "#6E5C4E", "#8F7B6A",
] as const;

// Initial centered items (visible before zoom)
export const INITIAL_CODE_BLOCK = {
  width: 320,
  height: 200,
  bg: "#0F172A",
  border: "#1E293B",
} as const;

export const INITIAL_SOCK = {
  width: 120,
  height: 160,
  color: "#8B6F5E",
  darnColor: "#D9944A",
} as const;

// Inline code comments for scattered tiles
export const INLINE_COMMENTS = [
  "// fixed null case",
  "// workaround for #412",
  "// TODO: refactor",
  "// temporary fix (2019)",
  "// don't touch this",
  "// legacy",
  "// patch for v2.3",
  "// hotfix",
] as const;

// Code snippet lines (fake syntax-highlighted code)
export const CODE_SNIPPETS = [
  ["if", "(", "user", ".", "role", " === ", "'admin'", ")"],
  ["return", " ", "fetchData", "(", "id", ")"],
  ["const", " ", "result", " = ", "await", " ", "parse", "(", "input", ")"],
  ["try", " { ", "validate", "(", "schema", ") }"],
  ["export", " ", "function", " ", "handleError", "(", "e", ")"],
  ["for", " (", "let", " i = 0; i < ", "items", ".length; i++)"],
] as const;
