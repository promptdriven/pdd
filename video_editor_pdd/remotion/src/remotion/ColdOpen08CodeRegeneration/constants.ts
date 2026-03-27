// ── Colors ──────────────────────────────────────────────
export const BG_COLOR = '#1E1E2E'; // VS Code / Catppuccin Mocha base
export const GUTTER_BG = '#181825'; // Slightly darker gutter
export const GUTTER_TEXT_COLOR = '#585B70'; // Line-number grey
export const SELECTION_COLOR = '#89B4FA'; // Blue selection highlight
export const SELECTION_OPACITY = 0.2;

// Catppuccin Mocha syntax palette
export const SYN_KEYWORD = '#CBA6F7'; // purple – def, return, if, for, in
export const SYN_FUNCTION = '#89B4FA'; // blue – function names
export const SYN_STRING = '#A6E3A1'; // green – strings
export const SYN_COMMENT = '#6C7086'; // grey – comments (patched code)
export const SYN_NUMBER = '#FAB387'; // peach – numbers
export const SYN_VARIABLE = '#CDD6F4'; // text – default variable color
export const SYN_OPERATOR = '#89DCEB'; // sky – operators
export const SYN_BUILTIN = '#F9E2AF'; // yellow – builtins (True, False, None, len)
export const SYN_DECORATOR = '#F38BA8'; // red – decorators, special
export const SYN_PARAM = '#EBA0AC'; // maroon – parameters
export const SYN_PUNCTUATION = '#BAC2DE'; // subtext1 – brackets, parens

// Terminal overlay
export const TERMINAL_BG = '#11111B';
export const TERMINAL_BG_OPACITY = 0.9;
export const TERMINAL_TEXT_COLOR = '#A6E3A1';
export const TERMINAL_BORDER_RADIUS = 8;

// ── Dimensions ──────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const EDITOR_PADDING_LEFT = 80; // gutter width
export const EDITOR_PADDING_TOP = 40;
export const CODE_LINE_HEIGHT = 22;
export const CODE_FONT_SIZE = 14;
export const TERMINAL_FONT_SIZE = 12;
export const GUTTER_WIDTH = 60;

// Terminal overlay dimensions
export const TERMINAL_WIDTH = 400;
export const TERMINAL_HEIGHT = 60;
export const TERMINAL_RIGHT = 40;
export const TERMINAL_BOTTOM = 40;

// ── Animation Phases (frames) ───────────────────────────
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
export const TOTAL_FRAMES = 60;

// ── Code Data ───────────────────────────────────────────

/** Token type for syntax colouring */
export type TokenType =
  | 'keyword'
  | 'function'
  | 'string'
  | 'comment'
  | 'number'
  | 'variable'
  | 'operator'
  | 'builtin'
  | 'decorator'
  | 'param'
  | 'punctuation'
  | 'plain';

export interface CodeToken {
  text: string;
  type: TokenType;
}

/** Map token types to colours */
export const TOKEN_COLOR_MAP: Record<TokenType, string> = {
  keyword: SYN_KEYWORD,
  function: SYN_FUNCTION,
  string: SYN_STRING,
  comment: SYN_COMMENT,
  number: SYN_NUMBER,
  variable: SYN_VARIABLE,
  operator: SYN_OPERATOR,
  builtin: SYN_BUILTIN,
  decorator: SYN_DECORATOR,
  param: SYN_PARAM,
  punctuation: SYN_PUNCTUATION,
  plain: SYN_VARIABLE,
};

/**
 * Patched function — 40 lines with ugly patch comments, TODOs, etc.
 * Each line is an array of tokens for syntax colouring.
 */
export const PATCHED_CODE: CodeToken[][] = [
  [{ text: 'def', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'process_order', type: 'function' }, { text: '(', type: 'punctuation' }, { text: 'order', type: 'param' }, { text: ',', type: 'punctuation' }, { text: ' ', type: 'plain' }, { text: 'ctx', type: 'param' }, { text: '):', type: 'punctuation' }],
  [{ text: '    ', type: 'plain' }, { text: '# PATCH: validate order schema (hotfix-2847)', type: 'comment' }],
  [{ text: '    ', type: 'plain' }, { text: 'if', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'not', type: 'keyword' }, { text: ' order', type: 'variable' }, { text: ':', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'raise', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'ValueError', type: 'builtin' }, { text: '(', type: 'punctuation' }, { text: '"empty order"', type: 'string' }, { text: ')', type: 'punctuation' }],
  [{ text: '    ', type: 'plain' }, { text: '# TODO: remove this after migration', type: 'comment' }],
  [{ text: '    ', type: 'plain' }, { text: 'legacy_flag', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'ctx', type: 'variable' }, { text: '.get(', type: 'punctuation' }, { text: '"use_legacy"', type: 'string' }, { text: ', ', type: 'punctuation' }, { text: 'False', type: 'builtin' }, { text: ')', type: 'punctuation' }],
  [{ text: '    ', type: 'plain' }, { text: 'if', type: 'keyword' }, { text: ' legacy_flag', type: 'variable' }, { text: ':', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: '# PATCH: legacy path workaround', type: 'comment' }],
  [{ text: '        ', type: 'plain' }, { text: 'items', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'order', type: 'variable' }, { text: '[', type: 'punctuation' }, { text: '"items"', type: 'string' }, { text: ']', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'total', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: '0', type: 'number' }],
  [{ text: '        ', type: 'plain' }, { text: 'for', type: 'keyword' }, { text: ' item ', type: 'variable' }, { text: 'in', type: 'keyword' }, { text: ' items', type: 'variable' }, { text: ':', type: 'punctuation' }],
  [{ text: '            ', type: 'plain' }, { text: 'price', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'item', type: 'variable' }, { text: '[', type: 'punctuation' }, { text: '"price"', type: 'string' }, { text: ']', type: 'punctuation' }],
  [{ text: '            ', type: 'plain' }, { text: '# FIXME: float precision issue', type: 'comment' }],
  [{ text: '            ', type: 'plain' }, { text: 'qty', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'item', type: 'variable' }, { text: '.get(', type: 'punctuation' }, { text: '"qty"', type: 'string' }, { text: ', ', type: 'punctuation' }, { text: '1', type: 'number' }, { text: ')', type: 'punctuation' }],
  [{ text: '            ', type: 'plain' }, { text: 'total', type: 'variable' }, { text: ' += ', type: 'operator' }, { text: 'price', type: 'variable' }, { text: ' * ', type: 'operator' }, { text: 'qty', type: 'variable' }],
  [{ text: '        ', type: 'plain' }, { text: 'order', type: 'variable' }, { text: '[', type: 'punctuation' }, { text: '"total"', type: 'string' }, { text: ']', type: 'punctuation' }, { text: ' = ', type: 'operator' }, { text: 'total', type: 'variable' }],
  [{ text: '    ', type: 'plain' }, { text: 'else', type: 'keyword' }, { text: ':', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'order', type: 'variable' }, { text: '[', type: 'punctuation' }, { text: '"total"', type: 'string' }, { text: ']', type: 'punctuation' }, { text: ' = ', type: 'operator' }, { text: 'compute_total', type: 'function' }, { text: '(order)', type: 'punctuation' }],
  [{ text: '', type: 'plain' }],
  [{ text: '    ', type: 'plain' }, { text: '# PATCH: discount logic (sprint-34)', type: 'comment' }],
  [{ text: '    ', type: 'plain' }, { text: 'discount', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'get_discount', type: 'function' }, { text: '(order, ctx)', type: 'punctuation' }],
  [{ text: '    ', type: 'plain' }, { text: 'if', type: 'keyword' }, { text: ' discount', type: 'variable' }, { text: ':', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'order', type: 'variable' }, { text: '[', type: 'punctuation' }, { text: '"total"', type: 'string' }, { text: ']', type: 'punctuation' }, { text: ' -= ', type: 'operator' }, { text: 'discount', type: 'variable' }],
  [{ text: '', type: 'plain' }],
  [{ text: '    ', type: 'plain' }, { text: '# TODO: tax calculation is duplicated', type: 'comment' }],
  [{ text: '    ', type: 'plain' }, { text: 'tax_rate', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'ctx', type: 'variable' }, { text: '.get(', type: 'punctuation' }, { text: '"tax_rate"', type: 'string' }, { text: ', ', type: 'punctuation' }, { text: '0.0', type: 'number' }, { text: ')', type: 'punctuation' }],
  [{ text: '    ', type: 'plain' }, { text: 'tax', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'order', type: 'variable' }, { text: '[', type: 'punctuation' }, { text: '"total"', type: 'string' }, { text: ']', type: 'punctuation' }, { text: ' * ', type: 'operator' }, { text: 'tax_rate', type: 'variable' }],
  [{ text: '    ', type: 'plain' }, { text: 'order', type: 'variable' }, { text: '[', type: 'punctuation' }, { text: '"tax"', type: 'string' }, { text: ']', type: 'punctuation' }, { text: ' = ', type: 'operator' }, { text: 'round', type: 'builtin' }, { text: '(tax, ', type: 'punctuation' }, { text: '2', type: 'number' }, { text: ')', type: 'punctuation' }],
  [{ text: '    ', type: 'plain' }, { text: 'order', type: 'variable' }, { text: '[', type: 'punctuation' }, { text: '"total"', type: 'string' }, { text: ']', type: 'punctuation' }, { text: ' += ', type: 'operator' }, { text: 'order', type: 'variable' }, { text: '[', type: 'punctuation' }, { text: '"tax"', type: 'string' }, { text: ']', type: 'punctuation' }],
  [{ text: '', type: 'plain' }],
  [{ text: '    ', type: 'plain' }, { text: '# Shipping — patched for intl', type: 'comment' }],
  [{ text: '    ', type: 'plain' }, { text: 'if', type: 'keyword' }, { text: ' ctx', type: 'variable' }, { text: '.get(', type: 'punctuation' }, { text: '"intl"', type: 'string' }, { text: '):', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'shipping', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'calc_intl_shipping', type: 'function' }, { text: '(order)', type: 'punctuation' }],
  [{ text: '    ', type: 'plain' }, { text: 'else', type: 'keyword' }, { text: ':', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'shipping', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'calc_shipping', type: 'function' }, { text: '(order)', type: 'punctuation' }],
  [{ text: '    ', type: 'plain' }, { text: 'order', type: 'variable' }, { text: '[', type: 'punctuation' }, { text: '"shipping"', type: 'string' }, { text: ']', type: 'punctuation' }, { text: ' = ', type: 'operator' }, { text: 'shipping', type: 'variable' }],
  [{ text: '    ', type: 'plain' }, { text: 'order', type: 'variable' }, { text: '[', type: 'punctuation' }, { text: '"total"', type: 'string' }, { text: ']', type: 'punctuation' }, { text: ' += ', type: 'operator' }, { text: 'shipping', type: 'variable' }],
  [{ text: '', type: 'plain' }],
  [{ text: '    ', type: 'plain' }, { text: 'order', type: 'variable' }, { text: '[', type: 'punctuation' }, { text: '"status"', type: 'string' }, { text: ']', type: 'punctuation' }, { text: ' = ', type: 'operator' }, { text: '"confirmed"', type: 'string' }],
  [{ text: '    ', type: 'plain' }, { text: 'return', type: 'keyword' }, { text: ' order', type: 'variable' }],
];

/**
 * Clean regenerated function — 30 lines, no patch comments, clean structure.
 */
export const REGENERATED_CODE: CodeToken[][] = [
  [{ text: 'def', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'process_order', type: 'function' }, { text: '(', type: 'punctuation' }, { text: 'order', type: 'param' }, { text: ',', type: 'punctuation' }, { text: ' ', type: 'plain' }, { text: 'ctx', type: 'param' }, { text: '):', type: 'punctuation' }],
  [{ text: '    ', type: 'plain' }, { text: 'validate_order', type: 'function' }, { text: '(order)', type: 'punctuation' }],
  [{ text: '', type: 'plain' }],
  [{ text: '    ', type: 'plain' }, { text: 'items', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'order', type: 'variable' }, { text: '[', type: 'punctuation' }, { text: '"items"', type: 'string' }, { text: ']', type: 'punctuation' }],
  [{ text: '    ', type: 'plain' }, { text: 'subtotal', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'sum', type: 'builtin' }, { text: '(', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'item', type: 'variable' }, { text: '[', type: 'punctuation' }, { text: '"price"', type: 'string' }, { text: ']', type: 'punctuation' }, { text: ' * ', type: 'operator' }, { text: 'item', type: 'variable' }, { text: '.get(', type: 'punctuation' }, { text: '"qty"', type: 'string' }, { text: ', ', type: 'punctuation' }, { text: '1', type: 'number' }, { text: ')', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'for', type: 'keyword' }, { text: ' item ', type: 'variable' }, { text: 'in', type: 'keyword' }, { text: ' items', type: 'variable' }],
  [{ text: '    ', type: 'plain' }, { text: ')', type: 'punctuation' }],
  [{ text: '', type: 'plain' }],
  [{ text: '    ', type: 'plain' }, { text: 'discount', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'compute_discount', type: 'function' }, { text: '(order, ctx)', type: 'punctuation' }],
  [{ text: '    ', type: 'plain' }, { text: 'tax', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'compute_tax', type: 'function' }, { text: '(', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'subtotal', type: 'variable' }, { text: ' - ', type: 'operator' }, { text: 'discount', type: 'variable' }, { text: ',', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'rate', type: 'param' }, { text: '=', type: 'operator' }, { text: 'ctx', type: 'variable' }, { text: '.tax_rate', type: 'punctuation' }],
  [{ text: '    ', type: 'plain' }, { text: ')', type: 'punctuation' }],
  [{ text: '', type: 'plain' }],
  [{ text: '    ', type: 'plain' }, { text: 'shipping', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'compute_shipping', type: 'function' }, { text: '(', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'order', type: 'variable' }, { text: ',', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'international', type: 'param' }, { text: '=', type: 'operator' }, { text: 'ctx', type: 'variable' }, { text: '.is_international', type: 'punctuation' }],
  [{ text: '    ', type: 'plain' }, { text: ')', type: 'punctuation' }],
  [{ text: '', type: 'plain' }],
  [{ text: '    ', type: 'plain' }, { text: 'total', type: 'variable' }, { text: ' = ', type: 'operator' }, { text: 'subtotal', type: 'variable' }, { text: ' - ', type: 'operator' }, { text: 'discount', type: 'variable' }, { text: ' + ', type: 'operator' }, { text: 'tax', type: 'variable' }, { text: ' + ', type: 'operator' }, { text: 'shipping', type: 'variable' }],
  [{ text: '', type: 'plain' }],
  [{ text: '    ', type: 'plain' }, { text: 'return', type: 'keyword' }, { text: ' ', type: 'plain' }, { text: 'Order', type: 'builtin' }, { text: '(', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'items', type: 'param' }, { text: '=', type: 'operator' }, { text: 'items', type: 'variable' }, { text: ',', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'subtotal', type: 'param' }, { text: '=', type: 'operator' }, { text: 'subtotal', type: 'variable' }, { text: ',', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'discount', type: 'param' }, { text: '=', type: 'operator' }, { text: 'discount', type: 'variable' }, { text: ',', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'tax', type: 'param' }, { text: '=', type: 'operator' }, { text: 'tax', type: 'variable' }, { text: ',', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'shipping', type: 'param' }, { text: '=', type: 'operator' }, { text: 'shipping', type: 'variable' }, { text: ',', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'total', type: 'param' }, { text: '=', type: 'operator' }, { text: 'total', type: 'variable' }, { text: ',', type: 'punctuation' }],
  [{ text: '        ', type: 'plain' }, { text: 'status', type: 'param' }, { text: '=', type: 'operator' }, { text: '"confirmed"', type: 'string' }],
  [{ text: '    ', type: 'plain' }, { text: ')', type: 'punctuation' }],
];

/** The function signature line (shared between patched and regenerated) */
export const FUNCTION_SIGNATURE: CodeToken[] = PATCHED_CODE[0];
