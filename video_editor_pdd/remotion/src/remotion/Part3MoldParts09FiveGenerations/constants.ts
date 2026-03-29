// ── Colors ──────────────────────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const PANEL_BG = "#1E1E2E";
export const PANEL_BORDER = "#334155";
export const HEADER_LABEL_COLOR = "#64748B";
export const LABEL_TEXT_COLOR = "#E2E8F0";

export const STATUS_RED = "#EF4444";
export const STATUS_YELLOW = "#FBBF24";
export const STATUS_GREEN = "#4ADE80";

// ── Dimensions ──────────────────────────────────────────────────────────────
export const CANVAS_W = 1920;
export const CANVAS_H = 1080;
export const PANEL_W = 320;
export const PANEL_H = 400;
export const PANEL_GAP = 24;
export const PANEL_COUNT = 5;
export const PANEL_TOTAL_W = PANEL_COUNT * PANEL_W + (PANEL_COUNT - 1) * PANEL_GAP; // 1696
export const PANEL_START_X = (CANVAS_W - PANEL_TOTAL_W) / 2; // 112
export const PANEL_Y = 220;
export const PANEL_RADIUS = 8;

export const STATUS_ICON_SIZE = 48;
export const LABEL_Y = 700;

// ── Timing (frames @ 30fps) ────────────────────────────────────────────────
export const TOTAL_FRAMES = 540;

// Panel appearance: panel 0 at frame 0, then 8-frame intervals
export const PANEL_FIRST_FRAME = 0;
export const PANEL_STAGGER = 8;
export const PANEL_SLIDE_DURATION = 20;

// Status stamps
export const RED_X_FRAME = 120;
export const YELLOW_WARN_FRAME = 150;
export const GREEN_CHECK_FRAME = 180;

// Winner highlight
export const HIGHLIGHT_FRAME = 240;
export const HIGHLIGHT_SCALE_DURATION = 20;
export const DIM_DURATION = 20;

// Label
export const LABEL_FRAME = 330;
export const LABEL_FADE_DURATION = 20;

// ── Per-generation faux code lines ──────────────────────────────────────────
export interface CodeLine {
  indent: number;
  tokens: { text: string; color: string }[];
}

export interface GenerationData {
  label: string;
  status: "fail" | "partial" | "pass";
  statusColor: string;
  failLines: number[]; // indices of lines that are "red-highlighted" for fails
  code: CodeLine[];
}

const KW = "#C678DD";    // purple keywords
const FN = "#61AFEF";    // blue functions
const STR = "#98C379";   // green strings
const NUM = "#D19A66";   // orange numbers
const CMT = "#5C6370";   // grey comments
const VAR = "#E5C07B";   // yellow vars
const TXT = "#ABB2BF";   // default text

const sharedCodeBase: CodeLine[] = [
  { indent: 0, tokens: [{ text: "export", color: KW }, { text: " ", color: TXT }, { text: "function", color: KW }, { text: " ", color: TXT }, { text: "validate", color: FN }, { text: "(input) {", color: TXT }] },
  { indent: 1, tokens: [{ text: "const", color: KW }, { text: " schema ", color: VAR }, { text: "= ", color: TXT }, { text: "buildSchema", color: FN }, { text: "();", color: TXT }] },
  { indent: 1, tokens: [{ text: "const", color: KW }, { text: " result ", color: VAR }, { text: "= schema.", color: TXT }, { text: "parse", color: FN }, { text: "(input);", color: TXT }] },
  { indent: 1, tokens: [{ text: "if", color: KW }, { text: " (!result.ok) {", color: TXT }] },
  { indent: 2, tokens: [{ text: "return", color: KW }, { text: " { error: result.msg };", color: TXT }] },
  { indent: 1, tokens: [{ text: "}", color: TXT }] },
  { indent: 1, tokens: [{ text: "return", color: KW }, { text: " { data: result.value };", color: TXT }] },
  { indent: 0, tokens: [{ text: "}", color: TXT }] },
];

function variantCode(tweakLine: number, tweakTokens: { text: string; color: string }[]): CodeLine[] {
  return sharedCodeBase.map((line, i) =>
    i === tweakLine ? { ...line, tokens: tweakTokens } : line
  );
}

export const GENERATIONS: GenerationData[] = [
  {
    label: "Gen 1",
    status: "fail",
    statusColor: STATUS_RED,
    failLines: [2, 4],
    code: variantCode(2, [
      { text: "const", color: KW }, { text: " result ", color: VAR },
      { text: "= schema.", color: TXT }, { text: "validate", color: FN }, { text: "(input);", color: TXT },
    ]),
  },
  {
    label: "Gen 2",
    status: "fail",
    statusColor: STATUS_RED,
    failLines: [3, 5],
    code: variantCode(3, [
      { text: "if", color: KW }, { text: " (result === ", color: TXT },
      { text: "null", color: NUM }, { text: ") {", color: TXT },
    ]),
  },
  {
    label: "Gen 3",
    status: "partial",
    statusColor: STATUS_YELLOW,
    failLines: [4],
    code: variantCode(4, [
      { text: "return", color: KW }, { text: " { error: ", color: TXT },
      { text: "\"invalid\"", color: STR }, { text: " };", color: TXT },
    ]),
  },
  {
    label: "Gen 4",
    status: "partial",
    statusColor: STATUS_YELLOW,
    failLines: [6],
    code: variantCode(6, [
      { text: "return", color: KW }, { text: " result.value;", color: TXT },
      { text: " // ", color: CMT }, { text: "unwrapped", color: CMT },
    ]),
  },
  {
    label: "Gen 5",
    status: "pass",
    statusColor: STATUS_GREEN,
    failLines: [],
    code: sharedCodeBase,
  },
];

export const BOTTOM_LABEL = "Generate five. Pick the one that passes all tests.";
