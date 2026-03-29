// === Layout & Canvas ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const TOTAL_FRAMES = 60;
export const FPS = 30;

// === Background & Editor Chrome ===
export const BG_COLOR = '#1E1E2E';
export const EDITOR_GUTTER_BG = '#181825';
export const LINE_NUMBER_COLOR = '#585B70';
export const SELECTION_COLOR = '#89B4FA';
export const SELECTION_OPACITY = 0.2;

// === Catppuccin Mocha Syntax Colors ===
export const SYN_KEYWORD = '#CBA6F7';   // purple — def, return, if, else, for, in, not, None, True, False, and, or
export const SYN_FUNCTION = '#89B4FA';   // blue — function names
export const SYN_STRING = '#A6E3A1';     // green — strings
export const SYN_COMMENT = '#6C7086';    // overlay1 — comments
export const SYN_NUMBER = '#FAB387';     // peach — numbers
export const SYN_PARAM = '#F5C2E7';      // pink — parameters
export const SYN_OPERATOR = '#89DCEB';   // sky — operators
export const SYN_VARIABLE = '#CDD6F4';   // text — variables
export const SYN_BUILTIN = '#F9E2AF';    // yellow — builtins like len, range, dict
export const SYN_DECORATOR = '#F9E2AF';  // yellow — decorators
export const SYN_PUNCTUATION = '#BAC2DE'; // subtext1 — brackets, parens, colons
export const SYN_SELF = '#F38BA8';        // red — self

// === Terminal ===
export const TERMINAL_BG = '#11111B';
export const TERMINAL_TEXT = '#A6E3A1';
export const TERMINAL_WIDTH = 400;
export const TERMINAL_HEIGHT = 60;
export const TERMINAL_RADIUS = 8;
export const TERMINAL_FONT_SIZE = 12;
export const TERMINAL_COMMAND = '$ pdd generate process_order ✓';

// === Code Font ===
export const CODE_FONT_FAMILY = 'JetBrains Mono, Fira Code, Consolas, monospace';
export const CODE_FONT_SIZE = 14;
export const CODE_LINE_HEIGHT = 22;

// === Editor Dimensions ===
export const EDITOR_PADDING_LEFT = 80;
export const EDITOR_PADDING_TOP = 40;
export const GUTTER_WIDTH = 60;

// === Animation Phase Boundaries (frames) ===
export const PHASE_SELECT_START = 0;
export const PHASE_SELECT_END = 8;
export const PHASE_DELETE_START = 8;
export const PHASE_DELETE_END = 12;
export const PHASE_VOID_START = 12;
export const PHASE_VOID_END = 14;
export const PHASE_REGEN_START = 14;
export const PHASE_REGEN_END = 44;
export const PHASE_TERMINAL_START = 38;
export const PHASE_TERMINAL_END = 48;
export const PHASE_HOLD_START = 48;
export const PHASE_HOLD_END = 60;

// Token types for syntax highlighting
export type TokenType =
  | 'keyword'
  | 'function'
  | 'string'
  | 'comment'
  | 'number'
  | 'param'
  | 'operator'
  | 'variable'
  | 'builtin'
  | 'decorator'
  | 'punctuation'
  | 'self'
  | 'plain';

export interface Token {
  text: string;
  type: TokenType;
}

export const TOKEN_COLORS: Record<TokenType, string> = {
  keyword: SYN_KEYWORD,
  function: SYN_FUNCTION,
  string: SYN_STRING,
  comment: SYN_COMMENT,
  number: SYN_NUMBER,
  param: SYN_PARAM,
  operator: SYN_OPERATOR,
  variable: SYN_VARIABLE,
  builtin: SYN_BUILTIN,
  decorator: SYN_DECORATOR,
  punctuation: SYN_PUNCTUATION,
  self: SYN_SELF,
  plain: SYN_VARIABLE,
};

// ============================================
// PATCHED CODE (40 lines — messy, with patch comments)
// ============================================
export const PATCHED_CODE: Token[][] = [
  // Line 1
  [{ text: 'def', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'process_order', type: 'function' }, { text: '(', type: 'punctuation' }, { text: 'order', type: 'param' }, { text: ',', type: 'punctuation' }, { text: ' ', type: 'plain' }, { text: 'ctx', type: 'param' }, { text: '):', type: 'punctuation' }],
  // Line 2
  [{ text: '    ', type: 'plain' }, { text: '# PATCH: validate order before processing', type: 'comment' }],
  // Line 3
  [{ text: '    ', type: 'plain' }, { text: 'if', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'not', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'order', type: 'variable' }, { text: ':', type: 'punctuation' }],
  // Line 4
  [{ text: '        ', type: 'plain' }, { text: 'return', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'None', type: 'keyword' }],
  // Line 5
  [{ text: '    ', type: 'plain' }, { text: '# TODO: remove this temp fix for issue #4521', type: 'comment' }],
  // Line 6
  [{ text: '    ', type: 'plain' }, { text: 'items', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'order', type: 'variable' }, { text: '.', type: 'punctuation' }, { text: 'get', type: 'function' }, { text: '(', type: 'punctuation' }, { text: '"items"', type: 'string' }, { text: ',', type: 'punctuation' }, { text: ' []', type: 'punctuation' }, { text: ')', type: 'punctuation' }],
  // Line 7
  [{ text: '    ', type: 'plain' }, { text: 'if', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'len', type: 'builtin' }, { text: '(', type: 'punctuation' }, { text: 'items', type: 'variable' }, { text: ')', type: 'punctuation' }, { text: ' == ', type: 'operator' }, { text: '0', type: 'number' }, { text: ':', type: 'punctuation' }],
  // Line 8
  [{ text: '        ', type: 'plain' }, { text: 'return', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'None', type: 'keyword' }],
  // Line 9
  [{ text: '    ', type: 'plain' }, { text: '# PATCH: hotfix for negative quantities', type: 'comment' }],
  // Line 10
  [{ text: '    ', type: 'plain' }, { text: 'total', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: '0', type: 'number' }],
  // Line 11
  [{ text: '    ', type: 'plain' }, { text: 'for', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'item', type: 'variable' }, { text: ' ', type: 'plain' }, { text: 'in', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'items', type: 'variable' }, { text: ':', type: 'punctuation' }],
  // Line 12
  [{ text: '        ', type: 'plain' }, { text: 'qty', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'item', type: 'variable' }, { text: '.', type: 'punctuation' }, { text: 'get', type: 'function' }, { text: '(', type: 'punctuation' }, { text: '"qty"', type: 'string' }, { text: ',', type: 'punctuation' }, { text: ' ', type: 'plain' }, { text: '0', type: 'number' }, { text: ')', type: 'punctuation' }],
  // Line 13
  [{ text: '        ', type: 'plain' }, { text: '# HACK: clamp negative to zero', type: 'comment' }],
  // Line 14
  [{ text: '        ', type: 'plain' }, { text: 'if', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'qty', type: 'variable' }, { text: ' < ', type: 'operator' }, { text: '0', type: 'number' }, { text: ':', type: 'punctuation' }],
  // Line 15
  [{ text: '            ', type: 'plain' }, { text: 'qty', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: '0', type: 'number' }],
  // Line 16
  [{ text: '        ', type: 'plain' }, { text: 'price', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'item', type: 'variable' }, { text: '.', type: 'punctuation' }, { text: 'get', type: 'function' }, { text: '(', type: 'punctuation' }, { text: '"price"', type: 'string' }, { text: ',', type: 'punctuation' }, { text: ' ', type: 'plain' }, { text: '0', type: 'number' }, { text: ')', type: 'punctuation' }],
  // Line 17
  [{ text: '        ', type: 'plain' }, { text: '# TODO: handle currency conversion', type: 'comment' }],
  // Line 18
  [{ text: '        ', type: 'plain' }, { text: 'subtotal', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'qty', type: 'variable' }, { text: ' * ', type: 'operator' }, { text: 'price', type: 'variable' }],
  // Line 19
  [{ text: '        ', type: 'plain' }, { text: 'total', type: 'variable' }, { text: ' += ', type: 'operator' }, { text: 'subtotal', type: 'variable' }],
  // Line 20
  [{ text: '    ', type: 'plain' }, { text: '# PATCH: apply discount if exists', type: 'comment' }],
  // Line 21
  [{ text: '    ', type: 'plain' }, { text: 'discount', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'ctx', type: 'variable' }, { text: '.', type: 'punctuation' }, { text: 'get', type: 'function' }, { text: '(', type: 'punctuation' }, { text: '"discount"', type: 'string' }, { text: ',', type: 'punctuation' }, { text: ' ', type: 'plain' }, { text: '0', type: 'number' }, { text: ')', type: 'punctuation' }],
  // Line 22
  [{ text: '    ', type: 'plain' }, { text: 'if', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'discount', type: 'variable' }, { text: ':', type: 'punctuation' }],
  // Line 23
  [{ text: '        ', type: 'plain' }, { text: '# FIXME: discount calc is wrong for %', type: 'comment' }],
  // Line 24
  [{ text: '        ', type: 'plain' }, { text: 'total', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'total', type: 'variable' }, { text: ' - ', type: 'operator' }, { text: 'discount', type: 'variable' }],
  // Line 25
  [{ text: '    ', type: 'plain' }, { text: 'if', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'total', type: 'variable' }, { text: ' < ', type: 'operator' }, { text: '0', type: 'number' }, { text: ':', type: 'punctuation' }],
  // Line 26
  [{ text: '        ', type: 'plain' }, { text: 'total', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: '0', type: 'number' }],
  // Line 27
  [{ text: '    ', type: 'plain' }, { text: 'tax_rate', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: '0.08', type: 'number' }],
  // Line 28
  [{ text: '    ', type: 'plain' }, { text: '# TODO: tax rate should come from ctx', type: 'comment' }],
  // Line 29
  [{ text: '    ', type: 'plain' }, { text: 'tax', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'total', type: 'variable' }, { text: ' * ', type: 'operator' }, { text: 'tax_rate', type: 'variable' }],
  // Line 30
  [{ text: '    ', type: 'plain' }, { text: 'grand_total', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'total', type: 'variable' }, { text: ' + ', type: 'operator' }, { text: 'tax', type: 'variable' }],
  // Line 31
  [{ text: '    ', type: 'plain' }, { text: 'result', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: '{', type: 'punctuation' }],
  // Line 32
  [{ text: '        ', type: 'plain' }, { text: '"subtotal"', type: 'string' }, { text: ':', type: 'punctuation' }, { text: ' ', type: 'plain' }, { text: 'total', type: 'variable' }, { text: ',', type: 'punctuation' }],
  // Line 33
  [{ text: '        ', type: 'plain' }, { text: '"tax"', type: 'string' }, { text: ':', type: 'punctuation' }, { text: ' ', type: 'plain' }, { text: 'tax', type: 'variable' }, { text: ',', type: 'punctuation' }],
  // Line 34
  [{ text: '        ', type: 'plain' }, { text: '"total"', type: 'string' }, { text: ':', type: 'punctuation' }, { text: ' ', type: 'plain' }, { text: 'grand_total', type: 'variable' }, { text: ',', type: 'punctuation' }],
  // Line 35
  [{ text: '        ', type: 'plain' }, { text: '"items"', type: 'string' }, { text: ':', type: 'punctuation' }, { text: ' ', type: 'plain' }, { text: 'len', type: 'builtin' }, { text: '(', type: 'punctuation' }, { text: 'items', type: 'variable' }, { text: ')', type: 'punctuation' }, { text: ',', type: 'punctuation' }],
  // Line 36
  [{ text: '    ', type: 'plain' }, { text: '}', type: 'punctuation' }],
  // Line 37
  [{ text: '    ', type: 'plain' }, { text: '# PATCH: log for debugging, remove later', type: 'comment' }],
  // Line 38
  [{ text: '    ', type: 'plain' }, { text: 'print', type: 'builtin' }, { text: '(', type: 'punctuation' }, { text: 'f"Order processed: {grand_total}"', type: 'string' }, { text: ')', type: 'punctuation' }],
  // Line 39
  [{ text: '    ', type: 'plain' }, { text: 'return', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'result', type: 'variable' }],
  // Line 40 (empty trailing line)
  [],
];

// ============================================
// REGENERATED CODE (30 lines — clean, no patch comments)
// ============================================
export const REGENERATED_CODE: Token[][] = [
  // Line 1
  [{ text: 'def', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'process_order', type: 'function' }, { text: '(', type: 'punctuation' }, { text: 'order', type: 'param' }, { text: ',', type: 'punctuation' }, { text: ' ', type: 'plain' }, { text: 'ctx', type: 'param' }, { text: '):', type: 'punctuation' }],
  // Line 2
  [{ text: '    ', type: 'plain' }, { text: 'items', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'validate_order_items', type: 'function' }, { text: '(', type: 'punctuation' }, { text: 'order', type: 'variable' }, { text: ')', type: 'punctuation' }],
  // Line 3
  [{ text: '    ', type: 'plain' }, { text: 'if', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'not', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'items', type: 'variable' }, { text: ':', type: 'punctuation' }],
  // Line 4
  [{ text: '        ', type: 'plain' }, { text: 'return', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'None', type: 'keyword' }],
  // Line 5
  [],
  // Line 6
  [{ text: '    ', type: 'plain' }, { text: 'subtotal', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'sum', type: 'builtin' }, { text: '(', type: 'punctuation' }],
  // Line 7
  [{ text: '        ', type: 'plain' }, { text: 'max', type: 'builtin' }, { text: '(', type: 'punctuation' }, { text: 'item', type: 'variable' }, { text: '.', type: 'punctuation' }, { text: 'quantity', type: 'variable' }, { text: ',', type: 'punctuation' }, { text: ' ', type: 'plain' }, { text: '0', type: 'number' }, { text: ')', type: 'punctuation' }, { text: ' * ', type: 'operator' }, { text: 'item', type: 'variable' }, { text: '.', type: 'punctuation' }, { text: 'unit_price', type: 'variable' }],
  // Line 8
  [{ text: '        ', type: 'plain' }, { text: 'for', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'item', type: 'variable' }, { text: ' ', type: 'plain' }, { text: 'in', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'items', type: 'variable' }],
  // Line 9
  [{ text: '    ', type: 'plain' }, { text: ')', type: 'punctuation' }],
  // Line 10
  [],
  // Line 11
  [{ text: '    ', type: 'plain' }, { text: 'discount', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'apply_discount', type: 'function' }, { text: '(', type: 'punctuation' }],
  // Line 12
  [{ text: '        ', type: 'plain' }, { text: 'subtotal', type: 'variable' }, { text: ',', type: 'punctuation' }],
  // Line 13
  [{ text: '        ', type: 'plain' }, { text: 'ctx', type: 'variable' }, { text: '.', type: 'punctuation' }, { text: 'discount_policy', type: 'variable' }],
  // Line 14
  [{ text: '    ', type: 'plain' }, { text: ')', type: 'punctuation' }],
  // Line 15
  [],
  // Line 16
  [{ text: '    ', type: 'plain' }, { text: 'tax', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'compute_tax', type: 'function' }, { text: '(', type: 'punctuation' }],
  // Line 17
  [{ text: '        ', type: 'plain' }, { text: 'subtotal', type: 'variable' }, { text: ' - ', type: 'operator' }, { text: 'discount', type: 'variable' }, { text: ',', type: 'punctuation' }],
  // Line 18
  [{ text: '        ', type: 'plain' }, { text: 'ctx', type: 'variable' }, { text: '.', type: 'punctuation' }, { text: 'tax_region', type: 'variable' }],
  // Line 19
  [{ text: '    ', type: 'plain' }, { text: ')', type: 'punctuation' }],
  // Line 20
  [],
  // Line 21
  [{ text: '    ', type: 'plain' }, { text: 'return', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'OrderResult', type: 'function' }, { text: '(', type: 'punctuation' }],
  // Line 22
  [{ text: '        ', type: 'plain' }, { text: 'subtotal', type: 'variable' }, { text: '=', type: 'operator' }, { text: 'subtotal', type: 'variable' }, { text: ',', type: 'punctuation' }],
  // Line 23
  [{ text: '        ', type: 'plain' }, { text: 'discount', type: 'variable' }, { text: '=', type: 'operator' }, { text: 'discount', type: 'variable' }, { text: ',', type: 'punctuation' }],
  // Line 24
  [{ text: '        ', type: 'plain' }, { text: 'tax', type: 'variable' }, { text: '=', type: 'operator' }, { text: 'tax', type: 'variable' }, { text: ',', type: 'punctuation' }],
  // Line 25
  [{ text: '        ', type: 'plain' }, { text: 'total', type: 'variable' }, { text: '=', type: 'operator' }, { text: 'subtotal', type: 'variable' }, { text: ' - ', type: 'operator' }, { text: 'discount', type: 'variable' }, { text: ' + ', type: 'operator' }, { text: 'tax', type: 'variable' }, { text: ',', type: 'punctuation' }],
  // Line 26
  [{ text: '        ', type: 'plain' }, { text: 'item_count', type: 'variable' }, { text: '=', type: 'operator' }, { text: 'len', type: 'builtin' }, { text: '(', type: 'punctuation' }, { text: 'items', type: 'variable' }, { text: ')', type: 'punctuation' }, { text: ',', type: 'punctuation' }],
  // Line 27
  [{ text: '    ', type: 'plain' }, { text: ')', type: 'punctuation' }],
  // Line 28
  [],
  // Line 29
  [],
  // Line 30
  [],
];

// Function signature shown during the "void" phase
export const FUNCTION_SIGNATURE: Token[][] = [
  [{ text: 'def', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'process_order', type: 'function' }, { text: '(', type: 'punctuation' }, { text: 'order', type: 'param' }, { text: ',', type: 'punctuation' }, { text: ' ', type: 'plain' }, { text: 'ctx', type: 'param' }, { text: '):', type: 'punctuation' }],
  [{ text: '    ', type: 'plain' }, { text: 'pass', type: 'keyword' }],
];
