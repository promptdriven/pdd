// ── Colors ──────────────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const BORDER_COLOR = "#334155";
export const HEADER_INVESTMENT_COLOR = "#64748B";
export const HEADER_PATCHING_COLOR = "#D9944A";
export const HEADER_PDD_COLOR = "#5AAA6E";
export const CELL_INVESTMENT_COLOR = "#E2E8F0";
export const CELL_PATCHING_COLOR = "#D9944A";
export const CELL_PDD_COLOR = "#5AAA6E";

// ── Layout ──────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TABLE_WIDTH = 1200;
export const TABLE_LEFT = (CANVAS_WIDTH - TABLE_WIDTH) / 2; // 360
export const TABLE_TOP = 280;
export const ROW_HEIGHT = 80;
export const COL_WIDTH = 400; // TABLE_WIDTH / 3
export const HEADER_UNDERLINE_Y = TABLE_TOP + 40;

// ── Typography ──────────────────────────────────────────────────────
export const HEADER_FONT_SIZE = 16;
export const CELL_FONT_SIZE = 18;
export const HEADER_FONT_WEIGHT = 600;
export const CELL_REGULAR_WEIGHT = 400;
export const CELL_BOLD_WEIGHT = 600;
export const HEADER_LETTER_SPACING = 2;

// ── Animation Frames ────────────────────────────────────────────────
export const TOTAL_FRAMES = 270;
export const HEADER_FADE_START = 0;
export const HEADER_FADE_DURATION = 20;
export const UNDERLINE_DRAW_DURATION = 15;

export const ROW1_START = 30;
export const ROW2_START = 70;
export const ROW3_START = 110;
export const ROW_SLIDE_DURATION = 25;
export const ROW_SLIDE_DISTANCE = 15;

export const GLOW_START = 150;
export const GLOW_DURATION = 40;
export const GLOW_SWEEP_WIDTH = 120;

// ── Table Data ──────────────────────────────────────────────────────
export interface TableRowData {
  investment: string;
  patching: string;
  pdd: string;
}

export const TABLE_ROWS: TableRowData[] = [
  {
    investment: "Fix a bug",
    patching: "One place, once",
    pdd: "Impossible forever",
  },
  {
    investment: "Improve code",
    patching: "One version",
    pdd: "All future versions",
  },
  {
    investment: "Document intent",
    patching: "One snapshot",
    pdd: "Living specification",
  },
];
