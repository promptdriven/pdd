// constants.ts — Part3MoldParts17ComponentTable

// Canvas
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = "#0A0F1A";

// Duration
export const DURATION_FRAMES = 300;
export const FPS = 30;

// Table layout
export const TABLE_WIDTH = 800;
export const TABLE_CENTER_X = (CANVAS_WIDTH - TABLE_WIDTH) / 2; // 560
export const TABLE_TOP_Y = 280;
export const COLUMN_WIDTHS = [200, 300, 300] as const;
export const HEADER_HEIGHT = 48;
export const ROW_HEIGHT = 60;
export const CELL_PADDING_V = 16;
export const CELL_PADDING_H = 24;
export const ACCENT_BORDER_WIDTH = 3;

// Colors — table structure
export const HEADER_BG = "#1E1E2E";
export const HEADER_BORDER_COLOR = "#334155";
export const HEADER_BORDER_WIDTH = 2;
export const ROW_BG = "#0F172A";
export const ROW_BORDER_COLOR = "#1E293B";
export const ROW_BORDER_WIDTH = 1;

// Colors — text
export const HEADER_TEXT_COLOR = "#64748B";
export const VALUE_TEXT_COLOR = "#E2E8F0";
export const PARENTHETICAL_TEXT_COLOR = "#94A3B8";
export const OWNER_TEXT_COLOR = "#CDD6F4";
export const HIERARCHY_TEXT_COLOR = "#E2E8F0";
export const SUBTEXT_COLOR = "#94A3B8";

// Colors — component accents
export const PROMPT_COLOR = "#D9944A";
export const GROUNDING_COLOR = "#4AD9A0";
export const TESTS_COLOR = "#4A90D9";

// Typography
export const FONT_FAMILY = "Inter, sans-serif";
export const HEADER_FONT_SIZE = 14;
export const HEADER_FONT_WEIGHT = 600;
export const HEADER_LETTER_SPACING = 2;
export const COMPONENT_FONT_SIZE = 16;
export const COMPONENT_FONT_WEIGHT = 700;
export const VALUE_FONT_SIZE = 16;
export const VALUE_FONT_WEIGHT = 400;
export const PARENTHETICAL_FONT_SIZE = 14;
export const HIERARCHY_FONT_SIZE = 18;
export const HIERARCHY_FONT_WEIGHT = 600;
export const HIERARCHY_EMPHASIS_WEIGHT = 700;
export const SUBTEXT_FONT_SIZE = 14;
export const SUBTEXT_FONT_WEIGHT = 400;

// Hierarchy text positions
export const HIERARCHY_Y = 620;
export const SUBTEXT_Y = 660;

// Animation timing (frames)
export const HEADER_FADE_START = 0;
export const HEADER_FADE_DURATION = 15;
export const ROW_SLIDE_START_BASE = 30;
export const ROW_SLIDE_INTERVAL = 30;
export const ROW_SLIDE_DURATION = 20;
export const ROW_SLIDE_DISTANCE = 40;
export const TESTS_GLOW_DURATION = 10;
export const TABLE_HOLD_START = 120;
export const HIERARCHY_FADE_START = 180;
export const HIERARCHY_FADE_DURATION = 20;
export const SUBTEXT_FADE_START = 240;
export const SUBTEXT_FADE_DURATION = 20;
export const PULSE_CYCLE_FRAMES = 30;
export const PULSE_GLOW_OPACITY = 0.15;
export const PULSE_GLOW_BLUR = 10;

// Table data
export interface TableRowData {
  component: string;
  encodes: string;
  parenthetical: string;
  owner: string;
  color: string;
}

export const TABLE_ROWS: TableRowData[] = [
  {
    component: "Prompt",
    encodes: "WHAT",
    parenthetical: "(intent)",
    owner: "Developer",
    color: PROMPT_COLOR,
  },
  {
    component: "Grounding",
    encodes: "HOW",
    parenthetical: "(style)",
    owner: "Automatic",
    color: GROUNDING_COLOR,
  },
  {
    component: "Tests",
    encodes: "CORRECTNESS",
    parenthetical: "",
    owner: "Accumulated",
    color: TESTS_COLOR,
  },
];

export const HEADER_COLUMNS = ["COMPONENT", "ENCODES", "OWNER"];
