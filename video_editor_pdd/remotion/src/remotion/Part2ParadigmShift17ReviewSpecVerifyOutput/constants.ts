// ── Colors ──────────────────────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const GRID_COLOR = "#1E293B";
export const GRID_OPACITY = 0.03;
export const PANEL_BG = "#1E293B";
export const TEXT_COLOR = "#E2E8F0";
export const AMBER_ACCENT = "#D9944A";
export const GREEN_ACCENT = "#5AAA6E";

// ── Dimensions ──────────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const GRID_SPACING = 60;

// ── Panel Positions ─────────────────────────────────────────────────────────
export const PROMPT_X = 200;
export const PROMPT_Y = 200;
export const PROMPT_WIDTH = 650;

export const TEST_X = 1050;
export const TEST_Y = 200;
export const TEST_WIDTH = 650;

export const PANEL_RADIUS = 8;
export const PANEL_PADDING = 24;

// ── Typography ──────────────────────────────────────────────────────────────
export const HEADER_FONT_SIZE = 12;
export const HEADER_LETTER_SPACING = 3;
export const PROMPT_TEXT_SIZE = 14;
export const TEST_NAME_SIZE = 14;
export const PASS_LABEL_SIZE = 12;
export const BOTTOM_LABEL_SIZE = 24;

// ── Animation Timing (frames @ 30fps) ──────────────────────────────────────
export const TOTAL_FRAMES = 360;
export const DISSOLVE_END = 45;
export const PROMPT_FADE_START = 45;
export const PROMPT_FADE_DURATION = 30;
export const TEST_FADE_START = 105;
export const TEST_FADE_DURATION = 30;
export const TEST_ROW_STAGGER = 12;
export const LABEL_START = 180;
export const LABEL_CHAR_DELAY = 2;
export const UNDERLINE_DELAY = 40;
export const UNDERLINE_DURATION = 20;
export const MORPH_START = 240;
export const MORPH_DURATION = 60;

// ── Data ────────────────────────────────────────────────────────────────────
export const PROMPT_LINES: string[] = [
  "# Counter Module Specification",
  "",
  "## Purpose",
  "Implement a thread-safe counter with",
  "increment, reset, and overflow handling.",
  "",
  "## Interface",
  "- increment() → void",
  "- reset() → void",
  "- value() → number",
  "",
  "## Behavior",
  "- Starts at zero on initialization",
  "- Increments by 1 on each call",
  "- Wraps to 0 at MAX_SAFE_INTEGER",
  "- Reset clears to initial state",
  "- All operations are atomic",
  "",
  "## Constraints",
  "- No external dependencies",
];

export interface TestResult {
  name: string;
  status: "pass";
}

export const TEST_RESULTS: TestResult[] = [
  { name: "test_counter_increments", status: "pass" },
  { name: "test_reset_clears_state", status: "pass" },
  { name: "test_overflow_wraps", status: "pass" },
  { name: "test_edge_case_zero", status: "pass" },
  { name: "test_concurrent_access", status: "pass" },
];

export const BOTTOM_LABEL_TEXT = "Review the spec. Verify the output.";

// ── Dissolve fake diff lines (visual only) ──────────────────────────────────
export const DIFF_LINES: string[] = [
  "+ function increment() {",
  "+   if (this.count >= MAX) {",
  "+     this.count = 0;",
  "-   this.count++;",
  "+   this.count = (this.count + 1);",
  "    return this.count;",
  "  }",
  "",
  "- function reset() {",
  "+   this.count = 0;",
  "+   this.dirty = false;",
  "  }",
  "",
  "+ function getValue(): number {",
  "+   return this.count;",
  "  }",
];
