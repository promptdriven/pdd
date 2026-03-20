// ── Colors ──────────────────────────────────────────────────────
export const BG_COLOR = "#0D1117";
export const GUTTER_BG = "#0D1117";
export const LINE_NUMBER_COLOR = "#484F58";
export const BASE_CODE_COLOR = "#C9D1D9";
export const KEYWORD_COLOR = "#FF7B72";
export const STRING_COLOR = "#A5D6FF";
export const COMMENT_COLOR = "#8B949E";
export const FUNCTION_NAME_COLOR = "#D2A8FF";
export const CURSOR_COLOR = "#58A6FF";
export const SCAN_LINE_COLOR = "#FFFFFF";

export const HIGHLIGHT_RED = "#F85149";
export const HIGHLIGHT_YELLOW = "#D29922";

// ── Dimensions ──────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const GUTTER_WIDTH = 200;
export const CODE_X_START = 210;
export const CODE_Y_START = 160;
export const CODE_X_END = 1720;
export const CODE_Y_END = 920;
export const FONT_SIZE = 18;
export const LINE_HEIGHT = 28;
export const LINE_NUMBER_FONT_SIZE = 14;
export const CURSOR_WIDTH = 2;
export const CURSOR_HEIGHT = 22;

// ── Timing ──────────────────────────────────────────────────────
export const TOTAL_FRAMES = 150;
export const FPS = 30;
export const HIGHLIGHT_START_FRAME = 10;
export const HIGHLIGHT_STAGGER = 8;
export const SCAN_LINE_START = 60;
export const SCAN_LINE_DURATION = 90;
export const CURSOR_ON_MS = 530;
export const CURSOR_OFF_MS = 530;

// ── Code Data ───────────────────────────────────────────────────
export const CODE_LINES: string[] = [
  "function processUserInput(raw: string): ProcessedInput {",
  "  const sanitized = raw.trim().toLowerCase();",
  "  let result: ProcessedInput;",
  "",
  "  // fixed null case",
  "  if (!sanitized || sanitized === 'undefined') {",
  "    return { valid: false, value: '', error: 'empty input' };",
  "  }",
  "",
  "  // workaround for #412",
  "  const cleaned = sanitized.replace(/[^\\w@.\\-]/g, '');",
  "  if (cleaned !== sanitized) {",
  "    result = { valid: true, value: cleaned, warning: 'chars stripped' };",
  "  // TODO: refactor this",
  "  } else if (cleaned.length > MAX_INPUT_LENGTH) {",
  "    result = { valid: true, value: cleaned.slice(0, MAX_INPUT_LENGTH) };",
  "  // legacy — do not touch",
  "  } else { result = { valid: true, value: cleaned }; }",
  "  return result;",
  "}",
];

export interface PatchScar {
  lineIndex: number; // 0-based index into CODE_LINES
  highlightColor: string;
  opacity: number;
}

export const PATCH_SCARS: PatchScar[] = [
  { lineIndex: 4, highlightColor: HIGHLIGHT_RED, opacity: 0.5 },
  { lineIndex: 9, highlightColor: HIGHLIGHT_RED, opacity: 0.5 },
  { lineIndex: 13, highlightColor: HIGHLIGHT_YELLOW, opacity: 0.4 },
  { lineIndex: 16, highlightColor: HIGHLIGHT_RED, opacity: 0.5 },
];
