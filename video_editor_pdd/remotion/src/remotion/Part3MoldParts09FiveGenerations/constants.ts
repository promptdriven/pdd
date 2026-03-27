// constants.ts — Part3MoldParts09FiveGenerations
// Colors, dimensions, generation data, and timing constants

// ─── Canvas ───────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BG_COLOR = "#0A0F1A";

// ─── Panel Layout ─────────────────────────────────────────────────────
export const PANEL_WIDTH = 320;
export const PANEL_HEIGHT = 400;
export const PANEL_GAP = 24;
export const PANEL_COUNT = 5;
export const TOTAL_PANELS_WIDTH =
  PANEL_COUNT * PANEL_WIDTH + (PANEL_COUNT - 1) * PANEL_GAP; // 1696
export const PANELS_START_X = (CANVAS_WIDTH - TOTAL_PANELS_WIDTH) / 2; // 112
export const PANEL_Y = 220;

export const PANEL_BG = "#1E1E2E";
export const PANEL_BORDER = "#334155";
export const PANEL_BORDER_RADIUS = 8;

// ─── Status Colors ────────────────────────────────────────────────────
export const FAIL_COLOR = "#EF4444";
export const WARN_COLOR = "#FBBF24";
export const PASS_COLOR = "#4ADE80";

// ─── Typography ───────────────────────────────────────────────────────
export const HEADER_FONT = "Inter, sans-serif";
export const CODE_FONT = "'JetBrains Mono', 'Fira Code', 'Consolas', monospace";
export const LABEL_FONT = "Inter, sans-serif";

export const HEADER_SIZE = 11;
export const CODE_SIZE = 10;
export const LABEL_SIZE = 20;

export const HEADER_COLOR = "#64748B";
export const LABEL_COLOR = "#E2E8F0";

// ─── Animation Timing (frames) ───────────────────────────────────────
export const PANEL_STAGGER = 8; // frames between each panel appearing
export const PANEL_SLIDE_DURATION = 20;
export const PANEL_SLIDE_DISTANCE = 30;

export const STATUS_FAIL_START = 120;
export const STATUS_WARN_START = 150;
export const STATUS_PASS_START = 180;

export const HIGHLIGHT_START = 240;
export const HIGHLIGHT_SCALE_DURATION = 20;
export const DIM_DURATION = 20;
export const DIM_OPACITY = 0.4;

export const LABEL_START = 330;
export const LABEL_FADE_DURATION = 20;

// ─── Status Icon Size ─────────────────────────────────────────────────
export const STATUS_ICON_SIZE = 48;

// ─── Generation Data ──────────────────────────────────────────────────
export type GenerationStatus = "fail" | "partial" | "pass";

export interface GenerationData {
  gen: number;
  status: GenerationStatus;
  icon: "x" | "warning" | "check";
  color: string;
}

export const GENERATIONS: GenerationData[] = [
  { gen: 1, status: "fail", icon: "x", color: FAIL_COLOR },
  { gen: 2, status: "fail", icon: "x", color: FAIL_COLOR },
  { gen: 3, status: "partial", icon: "warning", color: WARN_COLOR },
  { gen: 4, status: "partial", icon: "warning", color: WARN_COLOR },
  { gen: 5, status: "pass", icon: "check", color: PASS_COLOR },
];

// ─── Faux Code Lines for each generation ──────────────────────────────
export interface CodeLine {
  text: string;
  color: string;
  indent: number;
}

const KEYWORD = "#C792EA";
const STRING = "#C3E88D";
const FUNC = "#82AAFF";
const COMMENT = "#546E7A";
const VARIABLE = "#EEFFFF";
const NUMBER = "#F78C6C";
const TYPE = "#FFCB6B";
const ERROR_LINE = "#EF4444";

export const GEN_CODE: CodeLine[][] = [
  // Gen 1 — fails: wrong return type
  [
    { text: "export function validate(", indent: 0, color: KEYWORD },
    { text: "  input: string", indent: 1, color: TYPE },
    { text: "): boolean {", indent: 0, color: KEYWORD },
    { text: "  const parsed = parse(input);", indent: 1, color: VARIABLE },
    { text: "  return parsed.length;", indent: 1, color: ERROR_LINE },
    { text: "  // ^^^ returns number", indent: 1, color: COMMENT },
    { text: "}", indent: 0, color: KEYWORD },
  ],
  // Gen 2 — fails: missing null check
  [
    { text: "export function validate(", indent: 0, color: KEYWORD },
    { text: "  input: string", indent: 1, color: TYPE },
    { text: "): boolean {", indent: 0, color: KEYWORD },
    { text: "  const result = check(input);", indent: 1, color: VARIABLE },
    { text: "  return result.valid;", indent: 1, color: ERROR_LINE },
    { text: "  // ^^^ result can be null", indent: 1, color: COMMENT },
    { text: "}", indent: 0, color: KEYWORD },
  ],
  // Gen 3 — partial: edge case missed
  [
    { text: "export function validate(", indent: 0, color: KEYWORD },
    { text: "  input: string", indent: 1, color: TYPE },
    { text: "): boolean {", indent: 0, color: KEYWORD },
    { text: "  if (!input) return false;", indent: 1, color: FUNC },
    { text: "  const r = parse(input);", indent: 1, color: VARIABLE },
    { text: "  return r !== null;", indent: 1, color: VARIABLE },
    { text: "  // misses empty string", indent: 1, color: COMMENT },
    { text: "}", indent: 0, color: KEYWORD },
  ],
  // Gen 4 — partial: off-by-one
  [
    { text: "export function validate(", indent: 0, color: KEYWORD },
    { text: "  input: string", indent: 1, color: TYPE },
    { text: "): boolean {", indent: 0, color: KEYWORD },
    { text: "  if (!input) return false;", indent: 1, color: FUNC },
    { text: "  const len = input.length;", indent: 1, color: VARIABLE },
    { text: "  return len > 0 && len < 255;", indent: 1, color: VARIABLE },
    { text: "  // should be <= 255", indent: 1, color: COMMENT },
    { text: "}", indent: 0, color: KEYWORD },
  ],
  // Gen 5 — passes all tests
  [
    { text: "export function validate(", indent: 0, color: KEYWORD },
    { text: "  input: string", indent: 1, color: TYPE },
    { text: "): boolean {", indent: 0, color: KEYWORD },
    { text: "  if (!input?.trim()) return false;", indent: 1, color: FUNC },
    { text: "  const parsed = parse(input);", indent: 1, color: VARIABLE },
    { text: "  if (!parsed) return false;", indent: 1, color: FUNC },
    { text: "  return parsed.isValid();", indent: 1, color: STRING },
    { text: "}", indent: 0, color: KEYWORD },
  ],
];

// ─── Label Text ───────────────────────────────────────────────────────
export const BOTTOM_LABEL =
  "Generate five. Pick the one that passes all tests.";
