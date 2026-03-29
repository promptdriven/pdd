// ── Colors ──────────────────────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const WINDOW_FRAME_COLOR = "#1E293B";
export const TITLE_BAR_COLOR = "#151B28";
export const FILENAME_COLOR = "#E2E8F0";
export const ACCENT_AMBER = "#D9944A";
export const TEXT_COLOR = "#CBD5E1";
export const LINE_NUMBER_COLOR = "#64748B";

// ── Dimensions ──────────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const EDITOR_WIDTH = 1200;
export const EDITOR_HEIGHT = 700;
export const EDITOR_X = (CANVAS_WIDTH - EDITOR_WIDTH) / 2; // 360
export const EDITOR_Y = 160;
export const TITLE_BAR_HEIGHT = 36;
export const LINE_HEIGHT = 20;
export const GUTTER_WIDTH = 40;
export const GUTTER_INDICATOR_WIDTH = 3;
export const CORNER_RADIUS = 8;

// ── Typography ──────────────────────────────────────────────────────────────
export const MONO_FONT = "JetBrains Mono, monospace";
export const SANS_FONT = "Inter, sans-serif";
export const CODE_FONT_SIZE = 13;
export const LINE_NUMBER_SIZE = 12;
export const BADGE_FONT_SIZE = 11;
export const LABEL_FONT_SIZE = 15;

// ── Animation Timing (frames @ 30fps) ───────────────────────────────────────
export const WINDOW_FADE_IN_END = 30;
export const BADGE_START = 30;
export const BADGE_SCALE_DURATION = 15;
export const CONTENT_REVEAL_START = 30;
export const CONTENT_LINES_PER_FRAME = 1.5;
export const LABEL_FADE_IN_START = 180;
export const LABEL_FADE_IN_DURATION = 20;
export const FADE_OUT_START = 210;
export const FADE_OUT_DURATION = 30;
export const TOTAL_DURATION = 240;
export const TOTAL_LINES = 50;

// ── Prompt Content Lines ────────────────────────────────────────────────────
// Sections: header (1-3), spec (4-12), edge_case (13-22), error (23-35),
//           format (36-45), perf (46-50)

export interface PromptLineData {
  lineNumber: number;
  text: string;
  section: "header" | "spec" | "edge_case" | "error" | "format" | "perf";
  isHighlighted: boolean;
}

const line = (
  n: number,
  text: string,
  section: PromptLineData["section"],
  isHighlighted = false
): PromptLineData => ({ lineNumber: n, text, section, isHighlighted });

export const PROMPT_LINES: PromptLineData[] = [
  // ── Header (1-3) ──
  line(1, "# parser_v1 — Natural-language specification", "header"),
  line(2, "# Module: CSV-to-JSON transformer with validation", "header"),
  line(3, "", "header"),

  // ── Input format spec (4-12) ──
  line(4, "## Input Format Specification", "spec"),
  line(5, "- Accept CSV input via stdin or file path argument", "spec"),
  line(6, "- First row MUST be treated as column headers", "spec"),
  line(7, "- Support quoted fields containing commas and newlines", "spec"),
  line(8, "- Handle both \\r\\n and \\n line endings transparently", "spec"),
  line(9, "- Maximum field count per row: 256 columns", "spec"),
  line(10, "- Encoding: UTF-8 only; reject non-UTF-8 with error", "spec"),
  line(11, "- Empty file → return empty JSON array []", "spec"),
  line(12, "- Header-only file → return empty JSON array []", "spec"),

  // ── Edge case handling (13-22) — highlighted ──
  line(13, "## Edge Case Handling", "edge_case", true),
  line(14, "- Trailing comma on row → add null field at end", "edge_case", true),
  line(15, "- Mismatched column count → pad with null to header len", "edge_case", true),
  line(16, "- Unclosed quote at EOF → treat remainder as field value", "edge_case", true),
  line(17, "- Embedded double-quote → must be escaped as \"\"", "edge_case", true),
  line(18, "- Row with only whitespace → skip entirely", "edge_case", true),
  line(19, "- BOM marker at file start → strip silently", "edge_case", true),
  line(20, "- Null bytes in input → replace with U+FFFD", "edge_case", true),
  line(21, "- Field value \"null\" (string) ≠ null (missing)", "edge_case", true),
  line(22, "- Numeric strings → preserve as strings, never coerce", "edge_case", true),

  // ── Error handling rules (23-35) ──
  line(23, "## Error Handling Rules", "error"),
  line(24, "- All errors return JSON: { \"error\": \"...\", \"line\": N }", "error"),
  line(25, "- Invalid UTF-8 → error at first invalid byte position", "error"),
  line(26, "- File not found → exit code 1, error to stderr", "error"),
  line(27, "- Permission denied → exit code 2, specific message", "error"),
  line(28, "- Row exceeds 1MB → skip row, emit warning to stderr", "error"),
  line(29, "- Total input > 500MB → stream mode, do not buffer", "error"),
  line(30, "- Nested quotes without escape → error with column pos", "error"),
  line(31, "- Duplicate header names → append _2, _3, etc.", "error"),
  line(32, "- Header with empty name → rename to \"column_N\"", "error"),
  line(33, "- Control characters (0x00-0x1F) → strip except \\t, \\n", "error"),
  line(34, "- Circular reference in data → impossible for CSV, ignore", "error"),
  line(35, "- Timeout after 30s per 100MB of input", "error"),

  // ── Output format constraints (36-45) ──
  line(36, "## Output Format Constraints", "format"),
  line(37, "- Output valid JSON array of objects", "format"),
  line(38, "- Keys from header row, values from data rows", "format"),
  line(39, "- Indent: 2 spaces when --pretty flag is set", "format"),
  line(40, "- No trailing newline in compact mode", "format"),
  line(41, "- Number fields with >15 digits → output as strings", "format"),
  line(42, "- Date fields → keep as raw strings, never parse", "format"),
  line(43, "- Boolean-like values (true/false) → keep as strings", "format"),
  line(44, "- Preserve original field ordering from CSV headers", "format"),
  line(45, "- Output encoding: UTF-8 without BOM", "format"),

  // ── Performance requirements (46-50) ──
  line(46, "## Performance Requirements", "perf"),
  line(47, "- Process 100MB file in < 5 seconds on 4-core machine", "perf"),
  line(48, "- Memory usage: max 2x input file size", "perf"),
  line(49, "- Streaming mode for files > 500MB", "perf"),
  line(50, "- Exit code 0 on success, non-zero on any error", "perf"),
];
