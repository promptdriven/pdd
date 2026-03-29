// ── Canvas ──────────────────────────────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 840;

// ── Background & Document ───────────────────────────────────────────────────
export const BG_COLOR = "#0A0F1A";
export const DOC_BG = "#0F172A";
export const DOC_BORDER = "#1E293B";
export const DOC_WIDTH = 1000;
export const DOC_HEIGHT = 720;
export const DOC_X = (WIDTH - DOC_WIDTH) / 2; // 460
export const DOC_Y = 140;
export const DOC_PADDING = 48;
export const DOC_RADIUS = 12;

// ── Code Block ──────────────────────────────────────────────────────────────
export const CODE_BG = "#111827";
export const CODE_BORDER = "#334155";
export const CODE_ACCENT_COLOR = "#64748B";
export const CODE_ACCENT_WIDTH = 3;
export const CODE_RADIUS = 6;
export const CODE_GLOW_COLOR = "#4A90D9";
export const CODE_GLOW_OPACITY = 0.08;
export const CODE_TEXT_COLOR = "#A5F3FC";

// ── Typography Colors ───────────────────────────────────────────────────────
export const HEADING_COLOR = "#E2E8F0";
export const PROSE_COLOR = "#CBD5E1";
export const PROSE_OPACITY = 0.85;
export const ANNOTATION_NL_COLOR = "#D9944A";
export const ANNOTATION_CODE_COLOR = "#4A90D9";
export const ANNOTATION_OPACITY = 0.5;
export const BOTTOM_LABEL_COLOR = "#94A3B8";

// ── Typography Sizes ────────────────────────────────────────────────────────
export const HEADING_SIZE = 20;
export const PROSE_SIZE = 15;
export const CODE_SIZE = 13;
export const ANNOTATION_SIZE = 13;
export const BOTTOM_LABEL_SIZE = 18;

// ── Animation Keyframes ─────────────────────────────────────────────────────
export const DOC_FADE_IN_START = 0;
export const DOC_FADE_IN_END = 30;

export const PROSE_TOP_START = 0;
export const PROSE_TOP_END = 180; // text reveals over this range

export const CODE_BLOCK_START = 180;
export const CODE_BLOCK_ANIM_END = 200; // 20-frame scale-in
export const CODE_GLOW_END = 215; // glow finishes 15 frames after code start

export const PROSE_BOTTOM_START = 300;
export const PROSE_BOTTOM_END = 380;

export const ANNOTATION_START = 300;
export const ANNOTATION_DRAW_DURATION = 20;

export const BOTTOM_LABEL_START = 420;
export const BOTTOM_LABEL_FADE_DURATION = 20;

export const FADE_OUT_START = 780;
export const FADE_OUT_END = 840;

// ── Content ─────────────────────────────────────────────────────────────────
export const DOC_HEADING = "## Parser Module";

export const PROSE_ABOVE_LINES = [
  "Parse incoming JSON payloads according to the",
  "defined schema. Validate required fields, enforce",
  "type constraints, and normalize optional values.",
  "",
  "Handle malformed input by returning structured",
  "error objects with field-level diagnostics.",
  "Support nested objects up to 5 levels deep.",
  "",
  "Preserve original key ordering in output maps.",
  "Strip unknown keys silently unless strict mode",
  "is enabled via configuration flag.",
];

export const EMBEDDED_CODE_LINES = [
  "def compare_entries(a: Entry, b: Entry) -> int:",
  '    """Stable comparison for priority queue."""',
  "    if a.priority != b.priority:",
  "        return -1 if a.priority > b.priority else 1",
  "    if a.timestamp != b.timestamp:",
  "        return -1 if a.timestamp < b.timestamp else 1",
  "    # Fall back to insertion order for determinism",
  "    return a.seq - b.seq",
];

export const PROSE_BELOW_LINES = [
  "For all other formatting, follow standard",
  "conventions as defined in the style guide.",
  "Emit structured logs for each parse operation.",
  "Ensure idempotency across repeated invocations.",
];

export const BOTTOM_LABEL_TEXT =
  "The boundary between prompt and code is fluid.";
