// === Canvas ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = "#0A0F1A";
export const TOTAL_FRAMES = 90;
export const FPS = 30;

// === Mold Colors ===
export const NOZZLE_COLOR = "#D9944A";
export const WALLS_COLOR = "#4A90D9";
export const CAVITY_COLOR = "#4AD9A0";

// === Code Block ===
export const CODE_BLOCK_X = 660;
export const CODE_BLOCK_Y = 650;
export const CODE_BLOCK_WIDTH = 600;
export const CODE_BLOCK_HEIGHT = 250;
export const CODE_BG_COLOR = "#1E1E2E";
export const CODE_BORDER_COLOR = "#334155";
export const CODE_BORDER_FADED = "#1E293B";
export const CODE_GLOW_COLOR = "#38BDF8";
export const CODE_FONT_SIZE = 11;

// === Arrow ===
export const ARROW_COLOR = "#334155";
export const ARROW_OPACITY = 0.2;

// === Animation Keyframes (authoritative from JSON data) ===
export const CODE_GLOW_FADE_START = 20;
export const CODE_GLOW_FADE_END = 40;
export const CODE_GLOW_FROM = 0.2;
export const CODE_GLOW_TO = 0.0;

export const CODE_DIM_START = 20;
export const CODE_DIM_END = 40;
export const CODE_TEXT_FROM = 1.0;
export const CODE_TEXT_TO = 0.4;

export const MOLD_GLOW_START = 40;
export const MOLD_GLOW_END = 60;
export const MOLD_GLOW_FROM = 0.4;
export const MOLD_GLOW_TO = 0.6;

export const CODE_FADE_IN_DURATION = 15;

// === Python code snippet (syntax-highlighted tokens) ===
export interface CodeToken {
  text: string;
  color: string;
}

export type CodeLine = CodeToken[];

const KW = "#C678DD";   // keyword purple
const FN = "#61AFEF";   // function blue
const STR = "#98C379";  // string green
const NUM = "#D19A66";  // number orange
const CMT = "#5C6370";  // comment gray
const OP = "#ABB2BF";   // operator/default
const CLS = "#E5C07B";  // class/type yellow
const SELF = "#E06C75"; // self/special red

export const PYTHON_CODE: CodeLine[] = [
  [{ text: "class ", color: KW }, { text: "MoldConfig", color: CLS }, { text: ":", color: OP }],
  [{ text: "    def ", color: KW }, { text: "__init__", color: FN }, { text: "(", color: OP }, { text: "self", color: SELF }, { text: ", spec, tests):", color: OP }],
  [{ text: "        ", color: OP }, { text: "self", color: SELF }, { text: ".spec = spec", color: OP }],
  [{ text: "        ", color: OP }, { text: "self", color: SELF }, { text: ".tests = tests", color: OP }],
  [{ text: "        ", color: OP }, { text: "self", color: SELF }, { text: ".grounding = ", color: OP }, { text: "True", color: NUM }],
  [{ text: "", color: OP }],
  [{ text: "    def ", color: KW }, { text: "generate", color: FN }, { text: "(", color: OP }, { text: "self", color: SELF }, { text: "):", color: OP }],
  [{ text: "        ", color: OP }, { text: "# The code is output", color: CMT }],
  [{ text: "        ", color: OP }, { text: "return ", color: KW }, { text: "self", color: SELF }, { text: ".compile(", color: OP }, { text: "self", color: SELF }, { text: ".spec)", color: OP }],
  [{ text: "        ", color: OP }, { text: "# The mold is what matters", color: CMT }],
];
