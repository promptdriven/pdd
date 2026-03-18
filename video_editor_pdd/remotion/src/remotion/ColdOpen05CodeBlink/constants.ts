// ColdOpen05CodeBlink – constants & inline data
// Duration: 240 frames @ 30fps (8 seconds)

// ── Canvas ──────────────────────────────────────────
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 240;

// ── Colors ──────────────────────────────────────────
export const BG = '#0D1117';
export const LINE_NUMBER_COLOR = '#484F58';
export const TAB_TEXT_COLOR = '#C9D1D9';
export const STATUS_TEXT_COLOR = '#484F58';
export const SELECTION_COLOR = '#1F6FEB';
export const TERMINAL_GREEN = '#5AAA6E';

// Syntax highlighting colors
export const SYN_KEYWORD = '#FF7B72';
export const SYN_STRING = '#A5D6FF';
export const SYN_FUNCTION = '#D2A8FF';
export const SYN_COMMENT = '#8B949E';
export const SYN_VARIABLE = '#FFA657';
export const SYN_PAREN = '#C9D1D9';
export const SYN_TODO = '#EF4444';

// ── IDE Layout ──────────────────────────────────────
export const EDITOR_LEFT = 200; // line-number gutter width
export const EDITOR_RIGHT = 100;
export const TAB_BAR_HEIGHT = 80;
export const STATUS_BAR_HEIGHT = 60;
export const LINE_HEIGHT = 22;
export const CODE_FONT_SIZE = 14;
export const LINE_NUM_FONT_SIZE = 12;
export const TAB_FONT_SIZE = 12;
export const STATUS_FONT_SIZE = 10;
export const TERMINAL_FONT_SIZE = 11;

// ── Animation Timeline (frames) ────────────────────
export const PHASE_OLD_CODE_HOLD_END = 30; // 0-30: old code visible, cursor blinks
export const PHASE_SELECTION_START = 30; // 30-45: selection sweeps
export const PHASE_SELECTION_END = 45;
export const PHASE_TENSION_END = 60; // 45-60: hold selected
export const PHASE_DISSOLVE_START = 60; // 60-90: particle dissolution
export const PHASE_DISSOLVE_END = 90;
export const PHASE_VOID_END = 105; // 90-105: empty editor
export const PHASE_BLOCK1_START = 105; // 105-120: new code block 1
export const PHASE_BLOCK2_START = 120; // 120-135: new code block 2
export const PHASE_BLOCK3_START = 135; // 135-150: new code block 3
export const PHASE_TERMINAL_START = 150; // 150-180: terminal fades in
export const PHASE_HOLD_END = 240; // 180-240: hold

export const SELECTION_SWEEP_DURATION = 15;
export const PARTICLE_FADE_DURATION = 45;
export const BLOCK_REVEAL_DURATION = 12;
export const TERMINAL_FADE_DURATION = 20;

// ── Particle Dissolution ────────────────────────────
export const PARTICLE_COUNT = 200;
export const PARTICLE_GRAVITY = 0.3;
export const PARTICLE_MIN_SIZE = 2;
export const PARTICLE_MAX_SIZE = 4;

// ── Token types for syntax coloring ─────────────────
export type TokenType = 'keyword' | 'string' | 'function' | 'comment' | 'variable' | 'paren' | 'todo';

export interface Token {
  text: string;
  type: TokenType;
}

export interface CodeLine {
  tokens: Token[];
}

const kw = (text: string): Token => ({ text, type: 'keyword' });
const str = (text: string): Token => ({ text, type: 'string' });
const fn = (text: string): Token => ({ text, type: 'function' });
const cm = (text: string): Token => ({ text, type: 'comment' });
const vr = (text: string): Token => ({ text, type: 'variable' });
const pr = (text: string): Token => ({ text, type: 'paren' });
const td = (text: string): Token => ({ text, type: 'todo' });

// ── Old Code (18 lines) — messy with maintenance scars ──
export const OLD_CODE: CodeLine[] = [
  { tokens: [kw('def '), fn('parse_user'), pr('('), vr('raw_input'), pr(', '), vr('strict'), pr('='), kw('False'), pr('):') ] },
  { tokens: [pr('    '), vr('data'), pr(' = '), vr('raw_input'), pr('.'), fn('strip'), pr('()') ] },
  { tokens: [pr('    '), cm('# fixed null case') ] },
  { tokens: [pr('    '), kw('if '), vr('data'), kw(' is '), kw('None'), kw(' or '), vr('data'), pr(' == '), str('""'), pr(':') ] },
  { tokens: [pr('        '), kw('return '), kw('None') ] },
  { tokens: [pr('    '), vr('parts'), pr(' = '), vr('data'), pr('.'), fn('split'), pr('('), str('","'), pr(')') ] },
  { tokens: [pr('    '), cm('# workaround for #412') ] },
  { tokens: [pr('    '), kw('if '), fn('len'), pr('('), vr('parts'), pr(') < '), pr('2'), pr(':') ] },
  { tokens: [pr('        '), vr('parts'), pr('.'), fn('append'), pr('('), str('""'), pr(')') ] },
  { tokens: [pr('    '), td('# TODO: refactor this') ] },
  { tokens: [pr('    '), vr('name'), pr(' = '), vr('parts'), pr('['), pr('0'), pr(']'), pr('.'), fn('strip'), pr('()') ] },
  { tokens: [pr('    '), vr('email'), pr(' = '), vr('parts'), pr('['), pr('1'), pr(']'), pr('.'), fn('strip'), pr('()') ] },
  { tokens: [pr('    '), cm('# temporary fix (2019)') ] },
  { tokens: [pr('    '), kw('try'), pr(':') ] },
  { tokens: [pr('        '), vr('validated'), pr(' = '), fn('_validate_email'), pr('('), vr('email'), pr(')') ] },
  { tokens: [pr('    '), td("# don't remove — breaks prod") ] },
  { tokens: [pr('    '), kw('except'), pr(':') ] },
  { tokens: [pr('        '), vr('validated'), pr(' = '), vr('email') ] },
];

// ── New Code (14 lines) — clean, no comments ───────
export const NEW_CODE: CodeLine[] = [
  { tokens: [kw('def '), fn('parse_user'), pr('('), vr('raw_input'), pr(': '), vr('str'), pr(') -> '), vr('User'), pr(' | '), kw('None'), pr(':') ] },
  { tokens: [pr('    '), vr('data'), pr(' = '), vr('raw_input'), pr('.'), fn('strip'), pr('()') ] },
  { tokens: [pr('    '), kw('if not '), vr('data'), pr(':') ] },
  { tokens: [pr('        '), kw('return '), kw('None') ] },
  { tokens: [pr('') ] },
  { tokens: [pr('    '), vr('name'), pr(', '), vr('email'), pr(' = '), fn('_split_fields'), pr('('), vr('data'), pr(')') ] },
  { tokens: [pr('    '), vr('email'), pr(' = '), fn('validate_email'), pr('('), vr('email'), pr(')') ] },
  { tokens: [pr('') ] },
  { tokens: [pr('    '), kw('return '), fn('User'), pr('(') ] },
  { tokens: [pr('        '), vr('name'), pr('='), fn('normalize'), pr('('), vr('name'), pr('),') ] },
  { tokens: [pr('        '), vr('email'), pr('='), vr('email'), pr(',') ] },
  { tokens: [pr('        '), vr('source'), pr('='), str('"csv"'), pr(',') ] },
  { tokens: [pr('        '), vr('verified'), pr('='), kw('True'), pr(',') ] },
  { tokens: [pr('    '), pr(')') ] },
];

// Color map for token types
export const TOKEN_COLORS: Record<TokenType, string> = {
  keyword: SYN_KEYWORD,
  string: SYN_STRING,
  function: SYN_FUNCTION,
  comment: SYN_COMMENT,
  variable: SYN_VARIABLE,
  paren: SYN_PAREN,
  todo: SYN_TODO,
};
