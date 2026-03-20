// ── Colors ──────────────────────────────────────────────────────────────────
export const BG_COLOR = '#0D1117';
export const GUTTER_BG = '#161B22';
export const GUTTER_BORDER_COLOR = '#21262D';
export const LINE_NUMBER_COLOR = '#484F58';
export const CODE_TEXT_COLOR = '#C9D1D9';

// Syntax highlight palette (GitHub dark theme)
export const SYN_KEYWORD = '#FF7B72'; // function, return, const, if
export const SYN_TYPE = '#79C0FF'; // string, ProcessedInput, etc.
export const SYN_STRING = '#A5D6FF'; // string literals
export const SYN_IDENTIFIER = '#D2A8FF'; // function names
export const SYN_OPERATOR = '#FF7B72'; // =, !, &&, =>
export const SYN_BRACKET = '#C9D1D9'; // {, }, (, )
export const SYN_PROPERTY = '#79C0FF'; // object keys
export const SYN_BOOLEAN = '#79C0FF'; // true, false
export const SYN_REGEX = '#A5D6FF';
export const SYN_COMMENT = '#8B949E';
export const SYN_NUMBER = '#79C0FF';

// Phase-specific colors
export const SELECTION_HIGHLIGHT_COLOR = '#388BFD';
export const SELECTION_HIGHLIGHT_OPACITY = 0.15;
export const DISSOLUTION_GLOW_COLOR = '#F85149';
export const DISSOLUTION_GLOW_OPACITY = 0.03;
export const ENTRANCE_GLOW_COLOR = '#3FB950';
export const ENTRANCE_GLOW_OPACITY = 0.06;
export const CURSOR_COLOR = '#58A6FF';
export const CHECKMARK_COLOR = '#3FB950';
export const TERMINAL_BG = '#161B22';
export const TERMINAL_BORDER_COLOR = '#30363D';
export const TERMINAL_TEXT_COLOR = '#8B949E';

// ── Dimensions ──────────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const GUTTER_WIDTH = 60;
export const CODE_LEFT_PADDING = 80;
export const CODE_TOP_PADDING = 40;
export const LINE_HEIGHT = 28;
export const CODE_FONT_SIZE = 18;
export const TERMINAL_FONT_SIZE = 13;

// ── Timing (frames @ 30fps) ────────────────────────────────────────────────
export const FPS = 30;
export const TOTAL_FRAMES = 270;

export const SELECTION_START = 0;
export const SELECTION_END = 20;

export const DISSOLUTION_START = 20;
export const DISSOLUTION_END = 75;
export const DISSOLUTION_STAGGER_PER_LINE = 3;
export const PARTICLE_FADE_DURATION = 45;

export const EMPTY_BEAT_START = 75;
export const EMPTY_BEAT_END = 105;

export const REGEN_START = 105;
export const REGEN_END = 210;
export const CHARS_PER_SECOND = 60;

export const TERMINAL_START = 210;
export const TERMINAL_END = 270;
export const TERMINAL_FADE_FRAMES = 15;

// ── Code Data ───────────────────────────────────────────────────────────────

// The "patched" function from scene 0.6 (18 lines)
export const PATCHED_CODE_LINES: string[] = [
  'function processUserInput(raw: string): ProcessedInput {',
  '  const sanitized = raw.trim().toLowerCase();',
  '  // PATCH: handle empty after trim',
  '  if (!sanitized) {',
  "    return { valid: false, value: '', error: 'empty input' };",
  '  }',
  '  // PATCH: strip dangerous chars',
  "  const cleaned = sanitized.replace(/[^\\w@.\\-]/g, '');",
  '  // WORKAROUND: cap length for DB column',
  '  const truncated = cleaned.slice(0, MAX_INPUT_LENGTH);',
  '',
  '  // TODO: revisit this mapping',
  '  return {',
  '    valid: true,',
  '    value: truncated,',
  "    ...(cleaned !== sanitized && { warning: 'chars stripped' }),",
  '  };',
  '}',
];

// The clean regenerated function (14 lines, no comments/patches)
export const CLEAN_CODE_LINES: string[] = [
  'function processUserInput(raw: string): ProcessedInput {',
  '  const sanitized = raw.trim().toLowerCase();',
  '',
  '  if (!sanitized) {',
  "    return { valid: false, value: '', error: 'empty input' };",
  '  }',
  '',
  "  const cleaned = sanitized.replace(/[^\\w@.\\-]/g, '');",
  '  const truncated = cleaned.slice(0, MAX_INPUT_LENGTH);',
  '',
  '  return {',
  '    valid: true,',
  '    value: truncated,',
  "    ...(cleaned !== sanitized && { warning: 'chars stripped' }),",
  '  };',
  '}',
];

// ── Terminal ────────────────────────────────────────────────────────────────
export const TERMINAL_COMMAND = '$ pdd generate processUserInput';
export const TERMINAL_RESULT = ' ✓';
