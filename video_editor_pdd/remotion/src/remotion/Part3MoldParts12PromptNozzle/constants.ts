// ── Canvas ──
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 720;
export const BG_COLOR = "#0A0F1A";

// ── Grid ──
export const GRID_SPACING = 60;
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.05;

// ── Colors ──
export const AMBER = "#D9944A";
export const AMBER_GLOW = "#D9944A";
export const TEAL = "#0D9488";
export const WALL_BLUE = "#4A90D9";
export const TERMINAL_GREEN = "#A6E3A1";
export const SYNTAX_KEYWORD = "#C678DD";
export const SYNTAX_STRING = "#98C379";
export const SYNTAX_FUNC = "#61AFEF";
export const SYNTAX_COMMENT = "#5C6370";
export const SYNTAX_TYPE = "#E5C07B";
export const SYNTAX_DEFAULT = "#ABB2BF";

// ── Mold geometry (centered on canvas) ──
export const MOLD_CENTER_X = WIDTH / 2;
export const MOLD_TOP = 180;
export const MOLD_WIDTH = 600;
export const MOLD_HEIGHT = 500;
export const MOLD_WALL_THICKNESS = 8;
export const NOZZLE_WIDTH = 60;
export const NOZZLE_HEIGHT = 80;
export const NOZZLE_TIP_Y = MOLD_TOP;
export const NOZZLE_TOP_Y = MOLD_TOP - NOZZLE_HEIGHT;

// ── Cavity (inside the mold walls) ──
export const CAVITY_LEFT = MOLD_CENTER_X - MOLD_WIDTH / 2 + MOLD_WALL_THICKNESS + 20;
export const CAVITY_RIGHT = MOLD_CENTER_X + MOLD_WIDTH / 2 - MOLD_WALL_THICKNESS - 20;
export const CAVITY_TOP = MOLD_TOP + 30;
export const CAVITY_BOTTOM = MOLD_TOP + MOLD_HEIGHT - MOLD_WALL_THICKNESS - 20;
export const CAVITY_WIDTH = CAVITY_RIGHT - CAVITY_LEFT;
export const CAVITY_HEIGHT = CAVITY_BOTTOM - CAVITY_TOP;

// ── Nozzle labels ──
export const NOZZLE_LABELS = [
  {
    text: "intent",
    direction: "left" as const,
    x: MOLD_CENTER_X - 130,
    y: NOZZLE_TOP_Y + 10,
  },
  {
    text: "requirements",
    direction: "right" as const,
    x: MOLD_CENTER_X + 60,
    y: NOZZLE_TOP_Y + 10,
  },
  {
    text: "constraints",
    direction: "top" as const,
    x: MOLD_CENTER_X - 40,
    y: NOZZLE_TOP_Y - 30,
  },
];

// ── Prompt text ──
export const PROMPT_TEXT =
  "Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode.";
export const PROMPT_FILE = "user_parser.prompt";

// ── Code versions ──
export const CODE_VERSION_A = [
  { text: "def ", color: SYNTAX_KEYWORD },
  { text: "parse_user_id", color: SYNTAX_FUNC },
  { text: "(raw_input):", color: SYNTAX_DEFAULT },
  { text: "\n  ", color: SYNTAX_DEFAULT },
  { text: "# validate & extract", color: SYNTAX_COMMENT },
  { text: "\n  ", color: SYNTAX_DEFAULT },
  { text: "try", color: SYNTAX_KEYWORD },
  { text: ":", color: SYNTAX_DEFAULT },
  { text: "\n    cleaned = raw_input.strip()", color: SYNTAX_DEFAULT },
  { text: "\n    ", color: SYNTAX_DEFAULT },
  { text: "if not", color: SYNTAX_KEYWORD },
  { text: " cleaned:", color: SYNTAX_DEFAULT },
  { text: "\n      ", color: SYNTAX_DEFAULT },
  { text: "return", color: SYNTAX_KEYWORD },
  { text: " None", color: SYNTAX_TYPE },
  { text: "\n    uid = ", color: SYNTAX_DEFAULT },
  { text: "int", color: SYNTAX_FUNC },
  { text: "(cleaned)", color: SYNTAX_DEFAULT },
  { text: "\n    ", color: SYNTAX_DEFAULT },
  { text: "return", color: SYNTAX_KEYWORD },
  { text: " uid", color: SYNTAX_DEFAULT },
  { text: "\n  ", color: SYNTAX_DEFAULT },
  { text: "except", color: SYNTAX_KEYWORD },
  { text: ":", color: SYNTAX_DEFAULT },
  { text: "\n    ", color: SYNTAX_DEFAULT },
  { text: "return", color: SYNTAX_KEYWORD },
  { text: " None", color: SYNTAX_TYPE },
];

export const CODE_VERSION_B = [
  { text: "def ", color: SYNTAX_KEYWORD },
  { text: "extract_uid", color: SYNTAX_FUNC },
  { text: "(data):", color: SYNTAX_DEFAULT },
  { text: "\n  ", color: SYNTAX_DEFAULT },
  { text: "# safe parse", color: SYNTAX_COMMENT },
  { text: "\n  normalized = data.strip()", color: SYNTAX_DEFAULT },
  { text: "\n  ", color: SYNTAX_DEFAULT },
  { text: "if", color: SYNTAX_KEYWORD },
  { text: " ", color: SYNTAX_DEFAULT },
  { text: "len", color: SYNTAX_FUNC },
  { text: "(normalized) == 0:", color: SYNTAX_DEFAULT },
  { text: "\n    ", color: SYNTAX_DEFAULT },
  { text: "return", color: SYNTAX_KEYWORD },
  { text: " None", color: SYNTAX_TYPE },
  { text: "\n  ", color: SYNTAX_DEFAULT },
  { text: "try", color: SYNTAX_KEYWORD },
  { text: ":", color: SYNTAX_DEFAULT },
  { text: "\n    result = ", color: SYNTAX_DEFAULT },
  { text: "int", color: SYNTAX_FUNC },
  { text: "(normalized)", color: SYNTAX_DEFAULT },
  { text: "\n  ", color: SYNTAX_DEFAULT },
  { text: "except", color: SYNTAX_KEYWORD },
  { text: " (", color: SYNTAX_DEFAULT },
  { text: "ValueError", color: SYNTAX_TYPE },
  { text: ",", color: SYNTAX_DEFAULT },
  { text: " TypeError", color: SYNTAX_TYPE },
  { text: "):", color: SYNTAX_DEFAULT },
  { text: "\n    ", color: SYNTAX_DEFAULT },
  { text: "return", color: SYNTAX_KEYWORD },
  { text: " None", color: SYNTAX_TYPE },
  { text: "\n  ", color: SYNTAX_DEFAULT },
  { text: "return", color: SYNTAX_KEYWORD },
  { text: " result", color: SYNTAX_DEFAULT },
];

// ── Terminal commands ──
export const TERMINAL_COMMANDS = [
  { text: "$ pdd generate user_parser.prompt", frame: 300 },
  { text: "  → output: a3f7c2d", frame: 330 },
  { text: "$ pdd generate user_parser.prompt", frame: 360 },
  { text: "  → output: e1b94f8", frame: 390 },
];

// ── Animation timing (frame numbers) ──
export const PHASE_NOZZLE_GLOW_START = 0;
export const PHASE_NOZZLE_GLOW_END = 30;
export const PHASE_LABELS_START = 30;
export const PHASE_LABELS_STAGGER = 15;
export const PHASE_FILE_LABEL_START = 90;
export const PHASE_FILE_LABEL_DURATION = 60;
export const PHASE_TEXT_STREAM_START = 120;
export const PHASE_LIQUID_FILL_START = 240;
export const PHASE_DRAIN_START = 300;
export const PHASE_DRAIN_END = 360;
export const PHASE_REFILL_START = 360;
export const PHASE_REFILL_END = 480;
export const PHASE_DUAL_VIEW_START = 480;
export const PHASE_HOLD_START = 600;
