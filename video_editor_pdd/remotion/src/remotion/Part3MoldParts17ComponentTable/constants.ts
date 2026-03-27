// ─── Canvas ───
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BG_COLOR = "#0A0F1A";
export const FPS = 30;
export const DURATION_FRAMES = 300;

// ─── Table layout ───
export const TABLE_CENTER_X = 960;
export const TABLE_TOP_Y = 280;
export const TABLE_WIDTH = 800;
export const COLUMN_WIDTHS = [200, 300, 200] as const;
export const ROW_HEIGHT = 60;
export const CELL_PADDING_V = 16;
export const CELL_PADDING_H = 24;
export const ACCENT_BORDER_WIDTH = 3;

// ─── Table colors ───
export const HEADER_BG = "#1E1E2E";
export const HEADER_BORDER = "#334155";
export const ROW_BG = "#0F172A";
export const ROW_BORDER = "#1E293B";

// ─── Text colors ───
export const HEADER_TEXT_COLOR = "#64748B";
export const VALUE_TEXT_COLOR = "#E2E8F0";
export const PARENTHETICAL_COLOR = "#94A3B8";
export const OWNER_TEXT_COLOR = "#CDD6F4";
export const HIERARCHY_TEXT_COLOR = "#E2E8F0";
export const SUBTEXT_COLOR = "#94A3B8";

// ─── Component accent colors ───
export const PROMPT_COLOR = "#D9944A";
export const GROUNDING_COLOR = "#4AD9A0";
export const TESTS_COLOR = "#4A90D9";

// ─── Row data ───
export interface TableRowData {
  component: string;
  encodes: string;
  parenthetical: string;
  owner: string;
  accentColor: string;
}

export const TABLE_ROWS: TableRowData[] = [
  {
    component: "Prompt",
    encodes: "WHAT",
    parenthetical: "(intent)",
    owner: "Developer",
    accentColor: PROMPT_COLOR,
  },
  {
    component: "Grounding",
    encodes: "HOW",
    parenthetical: "(style)",
    owner: "Automatic",
    accentColor: GROUNDING_COLOR,
  },
  {
    component: "Tests",
    encodes: "CORRECTNESS",
    parenthetical: "",
    owner: "Accumulated",
    accentColor: TESTS_COLOR,
  },
];

// ─── Hierarchy text ───
export const HIERARCHY_Y = 620;
export const SUBTEXT_Y = 660;

// ─── Animation frame markers ───
export const HEADER_FADE_START = 0;
export const HEADER_FADE_DURATION = 15;
export const ROW_SLIDE_START_BASE = 30;
export const ROW_SLIDE_INTERVAL = 30;
export const ROW_SLIDE_DURATION = 20;
export const TESTS_GLOW_DURATION = 10;
export const HIERARCHY_FADE_START = 180;
export const HIERARCHY_FADE_DURATION = 20;
export const SUBTEXT_FADE_START = 240;
export const SUBTEXT_FADE_DURATION = 20;
export const PULSE_CYCLE_FRAMES = 30;
