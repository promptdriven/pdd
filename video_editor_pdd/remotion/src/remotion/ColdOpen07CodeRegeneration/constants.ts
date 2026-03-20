// ─── Colors ───────────────────────────────────────────────────────────
export const BG_COLOR = '#0D1117';
export const GUTTER_BG = '#161B22';
export const GUTTER_TEXT_COLOR = '#484F58';
export const CODE_TEXT_COLOR = '#C9D1D9';
export const SELECTION_COLOR = '#388BFD';
export const SELECTION_OPACITY = 0.15;
export const DISSOLUTION_GLOW_COLOR = '#F85149';
export const DISSOLUTION_GLOW_OPACITY = 0.03;
export const CURSOR_COLOR = '#58A6FF';
export const ENTRANCE_GLOW_COLOR = '#3FB950';
export const ENTRANCE_GLOW_OPACITY = 0.06;
export const TERMINAL_BG = '#161B22';
export const TERMINAL_BORDER_COLOR = '#30363D';
export const TERMINAL_TEXT_COLOR = '#8B949E';
export const TERMINAL_CHECK_COLOR = '#3FB950';

// ─── Syntax highlighting colors ───────────────────────────────────────
export const SYN_KEYWORD = '#FF7B72'; // function, const, return, if, etc.
export const SYN_STRING = '#A5D6FF';
export const SYN_TYPE = '#FFA657';
export const SYN_NUMBER = '#79C0FF';
export const SYN_COMMENT = '#8B949E';
export const SYN_PROPERTY = '#D2A8FF';
export const SYN_BOOLEAN = '#79C0FF';
export const SYN_REGEX = '#A5D6FF';
export const SYN_PUNCTUATION = '#C9D1D9';
export const SYN_PARAM = '#FFA657';

// ─── Dimensions ───────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const GUTTER_WIDTH = 60;
export const CODE_LEFT_PADDING = 80;
export const CODE_TOP_PADDING = 40;
export const LINE_HEIGHT = 28;
export const CODE_FONT_SIZE = 18;
export const TERMINAL_FONT_SIZE = 13;

// ─── Animation timing (frames) ───────────────────────────────────────
export const FPS = 30;
export const TOTAL_FRAMES = 270;

// Phase boundaries
export const SELECTION_START = 0;
export const SELECTION_END = 20;
export const DISSOLUTION_START = 20;
export const DISSOLUTION_END = 75;
export const EMPTY_BEAT_START = 75;
export const EMPTY_BEAT_END = 105;
export const REGEN_START = 105;
export const REGEN_END = 210;
export const TERMINAL_START = 210;
export const TERMINAL_END = 270;

// Dissolution params
export const DISSOLUTION_STAGGER_FRAMES = 3;
export const DISSOLUTION_PARTICLE_SIZE = 2;
export const DISSOLUTION_FADE_DURATION = 45;

// Typewriter params
export const CHARS_PER_SECOND = 130;
export const ENTRANCE_GLOW_FADE_FRAMES = 10;

// Cursor blink
export const CURSOR_BLINK_RATE = 15; // frames per half-cycle

// Terminal overlay position
export const TERMINAL_X = 1400;
export const TERMINAL_Y = 980;
export const TERMINAL_WIDTH = 480;
export const TERMINAL_HEIGHT = 80;

// ─── Code data ────────────────────────────────────────────────────────

/** The old 18-line patched function (with patch comments/workarounds) */
export const OLD_CODE_LINES: string[] = [
  'function processUserInput(raw: string): ProcessedInput {',
  '  const sanitized = raw.trim().toLowerCase();',
  '',
  '  // PATCH: handle empty input edge case',
  '  if (!sanitized) {',
  '    return { valid: false, value: \'\', error: \'empty input\' };',
  '  }',
  '',
  '  // TODO: revisit regex — copied from StackOverflow',
  '  const cleaned = sanitized.replace(/[^\\w@.\\-]/g, \'\');',
  '  // WORKAROUND: truncate to prevent overflow (issue #2847)',
  '  const truncated = cleaned.slice(0, MAX_INPUT_LENGTH);',
  '',
  '  return {',
  '    valid: true,',
  '    value: truncated,',
  '    // HACK: warn if chars were stripped',
  '    ...(cleaned !== sanitized && { warning: \'chars stripped\' }),',
  '  };',
  '}',
];

/** The new 14-line clean function (no comments, no workarounds) */
export const NEW_CODE_LINES: string[] = [
  'function processUserInput(raw: string): ProcessedInput {',
  '  const sanitized = raw.trim().toLowerCase();',
  '',
  '  if (!sanitized) {',
  '    return { valid: false, value: \'\', error: \'empty input\' };',
  '  }',
  '',
  '  const cleaned = sanitized.replace(/[^\\w@.\\-]/g, \'\');',
  '  const truncated = cleaned.slice(0, MAX_INPUT_LENGTH);',
  '',
  '  return {',
  '    valid: true,',
  '    value: truncated,',
  '    ...(cleaned !== sanitized && { warning: \'chars stripped\' }),',
  '  };',
  '}',
];
