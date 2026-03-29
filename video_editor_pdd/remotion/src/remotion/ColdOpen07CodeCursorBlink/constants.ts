// ── Colors (Catppuccin Mocha theme) ──────────────────────────────────
export const BG_COLOR = "#1E1E2E";
export const LINE_NUMBER_COLOR = "#6C7086";
export const CURSOR_COLOR = "#CDD6F4";
export const TEXT_COLOR = "#CDD6F4";

// Syntax highlight colors
export const KEYWORD_COLOR = "#CBA6F7"; // purple — def, return, if, else, for, in, not, is, None, True, False, try, except, raise
export const FUNCTION_COLOR = "#89B4FA"; // blue — function names
export const STRING_COLOR = "#A6E3A1"; // green — strings
export const TYPE_COLOR = "#F9E2AF"; // yellow — type annotations
export const OPERATOR_COLOR = "#89DCEB"; // teal — operators, brackets
export const PARAM_COLOR = "#F38BA8"; // red — special params / decorators
export const NUMBER_COLOR = "#FAB387"; // peach — numbers
export const COMMENT_COLOR = "#6C7086"; // overlay0 — standard comments

// Patch comment colors
export const PATCH_COMMENT_COLOR = "#6C7086";
export const TODO_COMMENT_COLOR = "#F9E2AF";
export const HOTFIX_COMMENT_COLOR = "#F38BA8";

// Patch age left-border colors
export const RECENT_PATCH_COLOR = "#A6E3A1";
export const OLD_PATCH_COLOR = "#A6E3A1";
export const MEDIUM_PATCH_COLOR = "#F9E2AF";

// ── Dimensions ───────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const LINE_HEIGHT = 24;
export const GUTTER_WIDTH = 60;
export const CODE_FONT_SIZE = 14;
export const LINE_NUMBER_FONT_SIZE = 12;
export const CODE_LEFT_PADDING = 12;
export const TOP_PADDING = 20;
export const CURSOR_BLINK_FRAMES = 15;
export const FADE_IN_DURATION = 10;

// ── Font ─────────────────────────────────────────────────────────────
export const CODE_FONT = "'JetBrains Mono', 'Fira Code', 'Cascadia Code', 'Consolas', monospace";

// ── Patch comment line indices (0-based for array) ───────────────────
export type PatchAge = "old" | "medium" | "recent";

export interface PatchComment {
  line: number; // 1-based line number
  text: string;
  age: PatchAge;
}

export const PATCH_COMMENTS: PatchComment[] = [
  { line: 5, text: "# PATCH: fixed null check", age: "old" },
  { line: 12, text: "# TODO: refactor this block", age: "old" },
  { line: 18, text: "# HOTFIX: edge case #1247", age: "medium" },
  { line: 23, text: "# PATCH: handle empty list", age: "recent" },
  { line: 31, text: "# PATCH: timezone fix", age: "medium" },
  { line: 37, text: "# HOTFIX: race condition", age: "recent" },
];

// ── Line highlight config ────────────────────────────────────────────
export interface LineHighlight {
  line: number;
  color: string;
  opacity: number;
}

export const LINE_HIGHLIGHTS: LineHighlight[] = [
  { line: 5, color: OLD_PATCH_COLOR, opacity: 0.05 },
  { line: 12, color: OLD_PATCH_COLOR, opacity: 0.05 },
  { line: 18, color: MEDIUM_PATCH_COLOR, opacity: 0.05 },
  { line: 23, color: RECENT_PATCH_COLOR, opacity: 0.15 },
  { line: 31, color: MEDIUM_PATCH_COLOR, opacity: 0.05 },
  { line: 37, color: RECENT_PATCH_COLOR, opacity: 0.15 },
];

// ── Code Token Types ─────────────────────────────────────────────────
export type TokenType =
  | "keyword"
  | "function"
  | "string"
  | "type"
  | "operator"
  | "param"
  | "number"
  | "comment"
  | "patch_comment"
  | "todo_comment"
  | "hotfix_comment"
  | "text";

export interface CodeToken {
  text: string;
  type: TokenType;
}

export function getTokenColor(type: TokenType): string {
  switch (type) {
    case "keyword":
      return KEYWORD_COLOR;
    case "function":
      return FUNCTION_COLOR;
    case "string":
      return STRING_COLOR;
    case "type":
      return TYPE_COLOR;
    case "operator":
      return OPERATOR_COLOR;
    case "param":
      return PARAM_COLOR;
    case "number":
      return NUMBER_COLOR;
    case "comment":
      return COMMENT_COLOR;
    case "patch_comment":
      return PATCH_COMMENT_COLOR;
    case "todo_comment":
      return TODO_COMMENT_COLOR;
    case "hotfix_comment":
      return HOTFIX_COMMENT_COLOR;
    case "text":
    default:
      return TEXT_COLOR;
  }
}

// ── The 40-line patched function ─────────────────────────────────────
// Each line is an array of tokens for syntax highlighting
export const CODE_LINES: CodeToken[][] = [
  // Line 1
  [
    { text: "def ", type: "keyword" },
    { text: "process_order", type: "function" },
    { text: "(", type: "operator" },
    { text: "order", type: "text" },
    { text: ": ", type: "operator" },
    { text: "Dict", type: "type" },
    { text: ", ", type: "operator" },
    { text: "ctx", type: "text" },
    { text: ": ", type: "operator" },
    { text: "Context", type: "type" },
    { text: ") -> ", type: "operator" },
    { text: "Result", type: "type" },
    { text: ":", type: "operator" },
  ],
  // Line 2
  [
    { text: '    """Process an incoming order through the pipeline."""', type: "string" },
  ],
  // Line 3
  [
    { text: "    ", type: "text" },
    { text: "if", type: "keyword" },
    { text: " ", type: "text" },
    { text: "not", type: "keyword" },
    { text: " order:", type: "text" },
  ],
  // Line 4
  [
    { text: "        ", type: "text" },
    { text: "return", type: "keyword" },
    { text: " Result(", type: "text" },
    { text: "success", type: "text" },
    { text: "=", type: "operator" },
    { text: "False", type: "keyword" },
    { text: ", ", type: "operator" },
    { text: "error", type: "text" },
    { text: "=", type: "operator" },
    { text: '"empty order"', type: "string" },
    { text: ")", type: "operator" },
  ],
  // Line 5 — PATCH comment
  [
    { text: "    # PATCH: fixed null check", type: "patch_comment" },
  ],
  // Line 6
  [
    { text: "    items = order.", type: "text" },
    { text: "get", type: "function" },
    { text: "(", type: "operator" },
    { text: '"items"', type: "string" },
    { text: ", [])", type: "text" },
  ],
  // Line 7
  [
    { text: "    validated = []", type: "text" },
  ],
  // Line 8
  [
    { text: "    ", type: "text" },
    { text: "for", type: "keyword" },
    { text: " item ", type: "text" },
    { text: "in", type: "keyword" },
    { text: " items:", type: "text" },
  ],
  // Line 9
  [
    { text: "        ", type: "text" },
    { text: "if", type: "keyword" },
    { text: " item ", type: "text" },
    { text: "is", type: "keyword" },
    { text: " ", type: "text" },
    { text: "None", type: "keyword" },
    { text: ":", type: "operator" },
  ],
  // Line 10
  [
    { text: "            ", type: "text" },
    { text: "continue", type: "keyword" },
  ],
  // Line 11
  [
    { text: "        price = ", type: "text" },
    { text: "calculate_price", type: "function" },
    { text: "(item, ctx.", type: "text" },
    { text: "region", type: "text" },
    { text: ")", type: "operator" },
  ],
  // Line 12 — TODO comment
  [
    { text: "        # TODO: refactor this block", type: "todo_comment" },
  ],
  // Line 13
  [
    { text: "        ", type: "text" },
    { text: "if", type: "keyword" },
    { text: " price <= ", type: "text" },
    { text: "0", type: "number" },
    { text: ":", type: "operator" },
  ],
  // Line 14
  [
    { text: "            ", type: "text" },
    { text: "logger", type: "text" },
    { text: ".", type: "operator" },
    { text: "warn", type: "function" },
    { text: "(", type: "operator" },
    { text: 'f"Invalid price for {item[\'id\']}"', type: "string" },
    { text: ")", type: "operator" },
  ],
  // Line 15
  [
    { text: "            ", type: "text" },
    { text: "continue", type: "keyword" },
  ],
  // Line 16
  [
    { text: "        discount = ", type: "text" },
    { text: "apply_discount", type: "function" },
    { text: "(item, ctx.", type: "text" },
    { text: "promo_code", type: "text" },
    { text: ")", type: "operator" },
  ],
  // Line 17
  [
    { text: "        tax = ", type: "text" },
    { text: "compute_tax", type: "function" },
    { text: "(price - discount, ctx.", type: "text" },
    { text: "region", type: "text" },
    { text: ")", type: "operator" },
  ],
  // Line 18 — HOTFIX comment
  [
    { text: "        # HOTFIX: edge case #1247", type: "hotfix_comment" },
  ],
  // Line 19
  [
    { text: "        ", type: "text" },
    { text: "if", type: "keyword" },
    { text: " tax < ", type: "text" },
    { text: "0", type: "number" },
    { text: ":", type: "operator" },
  ],
  // Line 20
  [
    { text: "            tax = ", type: "text" },
    { text: "0", type: "number" },
  ],
  // Line 21
  [
    { text: "        final = price - discount + tax", type: "text" },
  ],
  // Line 22
  [
    { text: "        validated.", type: "text" },
    { text: "append", type: "function" },
    { text: "({", type: "operator" },
  ],
  // Line 23 — PATCH comment (cursor line)
  [
    { text: "    # PATCH: handle empty list", type: "patch_comment" },
  ],
  // Line 24
  [
    { text: '            "id"', type: "string" },
    { text: ": item[", type: "text" },
    { text: '"id"', type: "string" },
    { text: "],", type: "operator" },
  ],
  // Line 25
  [
    { text: '            "price"', type: "string" },
    { text: ": final,", type: "text" },
  ],
  // Line 26
  [
    { text: '            "tax"', type: "string" },
    { text: ": tax,", type: "text" },
  ],
  // Line 27
  [
    { text: "        })", type: "operator" },
  ],
  // Line 28
  [{ text: "", type: "text" }],
  // Line 29
  [
    { text: "    ", type: "text" },
    { text: "if", type: "keyword" },
    { text: " ", type: "text" },
    { text: "not", type: "keyword" },
    { text: " validated:", type: "text" },
  ],
  // Line 30
  [
    { text: "        ", type: "text" },
    { text: "return", type: "keyword" },
    { text: " Result(", type: "text" },
    { text: "success", type: "text" },
    { text: "=", type: "operator" },
    { text: "False", type: "keyword" },
    { text: ", ", type: "operator" },
    { text: "error", type: "text" },
    { text: "=", type: "operator" },
    { text: '"no valid items"', type: "string" },
    { text: ")", type: "operator" },
  ],
  // Line 31 — PATCH comment
  [
    { text: "    # PATCH: timezone fix", type: "patch_comment" },
  ],
  // Line 32
  [
    { text: "    ts = ", type: "text" },
    { text: "normalize_timestamp", type: "function" },
    { text: "(ctx.", type: "text" },
    { text: "now", type: "text" },
    { text: "(), ctx.", type: "text" },
    { text: "timezone", type: "text" },
    { text: ")", type: "operator" },
  ],
  // Line 33
  [
    { text: "    ", type: "text" },
    { text: "try", type: "keyword" },
    { text: ":", type: "operator" },
  ],
  // Line 34
  [
    { text: "        receipt = ", type: "text" },
    { text: "create_receipt", type: "function" },
    { text: "(validated, ts, ctx.", type: "text" },
    { text: "user_id", type: "text" },
    { text: ")", type: "operator" },
  ],
  // Line 35
  [
    { text: "    ", type: "text" },
    { text: "except", type: "keyword" },
    { text: " ", type: "text" },
    { text: "ReceiptError", type: "type" },
    { text: " ", type: "text" },
    { text: "as", type: "keyword" },
    { text: " e:", type: "text" },
  ],
  // Line 36
  [
    { text: "        ", type: "text" },
    { text: "logger", type: "text" },
    { text: ".", type: "operator" },
    { text: "error", type: "function" },
    { text: "(", type: "operator" },
    { text: 'f"Receipt failed: {e}"', type: "string" },
    { text: ")", type: "operator" },
  ],
  // Line 37 — HOTFIX comment
  [
    { text: "    # HOTFIX: race condition", type: "hotfix_comment" },
  ],
  // Line 38
  [
    { text: "        ", type: "text" },
    { text: "raise", type: "keyword" },
  ],
  // Line 39
  [{ text: "", type: "text" }],
  // Line 40
  [
    { text: "    ", type: "text" },
    { text: "return", type: "keyword" },
    { text: " Result(", type: "text" },
    { text: "success", type: "text" },
    { text: "=", type: "operator" },
    { text: "True", type: "keyword" },
    { text: ", ", type: "operator" },
    { text: "receipt", type: "text" },
    { text: "=receipt)", type: "text" },
  ],
];
