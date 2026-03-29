// === Colors (Catppuccin Mocha theme) ===
export const BG_COLOR = '#1E1E2E';
export const EDITOR_GUTTER_BG = '#181825';
export const LINE_NUMBER_COLOR = '#585B70';
export const SELECTION_COLOR = '#89B4FA';
export const SELECTION_OPACITY = 0.2;

// Syntax highlighting colors (Catppuccin Mocha)
export const SYN_KEYWORD = '#CBA6F7';    // purple - def, return, if, else, for, in, not, None, True, False
export const SYN_FUNCTION = '#89B4FA';   // blue - function names
export const SYN_STRING = '#A6E3A1';     // green - strings
export const SYN_COMMENT = '#6C7086';    // overlay1 - comments
export const SYN_PARAMETER = '#F38BA8';  // red - parameters
export const SYN_OPERATOR = '#89DCEB';   // sky - operators
export const SYN_NUMBER = '#FAB387';     // peach - numbers
export const SYN_BUILTIN = '#F9E2AF';    // yellow - builtins like len, dict, list
export const SYN_SELF = '#F38BA8';       // red - self
export const SYN_PLAIN = '#CDD6F4';      // text - plain identifiers
export const SYN_DECORATOR = '#F9E2AF';  // yellow - decorators
export const SYN_PATCH = '#F38BA8';      // red - patch markers

// Terminal
export const TERMINAL_BG = '#11111B';
export const TERMINAL_TEXT = '#A6E3A1';
export const TERMINAL_BORDER_RADIUS = 8;

// === Dimensions ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const GUTTER_WIDTH = 60;
export const LINE_HEIGHT = 22;
export const CODE_FONT_SIZE = 14;
export const CODE_PADDING_LEFT = 16;
export const CODE_PADDING_TOP = 40;
export const TERMINAL_WIDTH = 420;
export const TERMINAL_HEIGHT = 60;
export const TERMINAL_FONT_SIZE = 12;
export const TERMINAL_MARGIN = 24;

// === Animation Phases (frame ranges) ===
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
export const ORIGINAL_LINE_COUNT = 40;
export const REGEN_LINE_COUNT = 30;
export const LINES_PER_SELECTION_FRAME = 5;

// === Patched (old) code — simulated 40-line function with patch comments ===
export interface CodeToken {
  text: string;
  color: string;
}

export type CodeLine = CodeToken[];

function kw(text: string): CodeToken { return { text, color: SYN_KEYWORD }; }
function fn(text: string): CodeToken { return { text, color: SYN_FUNCTION }; }
function str(text: string): CodeToken { return { text, color: SYN_STRING }; }
function cmt(text: string): CodeToken { return { text, color: SYN_COMMENT }; }
function param(text: string): CodeToken { return { text, color: SYN_PARAMETER }; }
function op(text: string): CodeToken { return { text, color: SYN_OPERATOR }; }
function num(text: string): CodeToken { return { text, color: SYN_NUMBER }; }
function blt(text: string): CodeToken { return { text, color: SYN_BUILTIN }; }
function slf(text: string): CodeToken { return { text, color: SYN_SELF }; }
function pl(text: string): CodeToken { return { text, color: SYN_PLAIN }; }
function patch(text: string): CodeToken { return { text, color: SYN_PATCH }; }

export const PATCHED_CODE: CodeLine[] = [
  [kw('def'), pl(' '), fn('process_order'), pl('('), param('order'), pl(', '), param('ctx'), pl('):')],
  [pl('    '), cmt('# PATCH: validate order before processing')],
  [pl('    '), kw('if'), pl(' '), kw('not'), pl(' '), pl('order'), pl('.'), pl('items'), pl(':')],
  [pl('        '), kw('raise'), pl(' '), blt('ValueError'), pl('('), str('"Empty order"'), pl(')')],
  [pl('    '), cmt('# TODO: remove this workaround after v2.3')],
  [pl('    '), pl('total'), pl(' '), op('='), pl(' '), num('0')],
  [pl('    '), pl('discounts'), pl(' '), op('='), pl(' '), blt('dict'), pl('()')],
  [pl('    '), cmt('# PATCH: handle legacy discount format')],
  [pl('    '), kw('for'), pl(' '), pl('item'), pl(' '), kw('in'), pl(' '), pl('order'), pl('.'), pl('items'), pl(':')],
  [pl('        '), kw('if'), pl(' '), pl('item'), pl('.'), pl('discount_type'), pl(' '), op('=='), pl(' '), str('"legacy"'), pl(':')],
  [pl('            '), pl('disc'), pl(' '), op('='), pl(' '), pl('item'), pl('.'), pl('price'), pl(' '), op('*'), pl(' '), num('0.1')],
  [pl('        '), kw('elif'), pl(' '), pl('item'), pl('.'), pl('discount_type'), pl(' '), op('=='), pl(' '), str('"promo"'), pl(':')],
  [pl('            '), pl('disc'), pl(' '), op('='), pl(' '), pl('item'), pl('.'), pl('price'), pl(' '), op('*'), pl(' '), num('0.15')],
  [pl('        '), kw('else'), pl(':')],
  [pl('            '), pl('disc'), pl(' '), op('='), pl(' '), num('0')],
  [pl('        '), cmt('# PATCH: accumulate discount per category')],
  [pl('        '), pl('cat'), pl(' '), op('='), pl(' '), pl('item'), pl('.'), pl('category')],
  [pl('        '), kw('if'), pl(' '), pl('cat'), pl(' '), kw('not'), pl(' '), kw('in'), pl(' '), pl('discounts'), pl(':')],
  [pl('            '), pl('discounts'), pl('['), pl('cat'), pl(']'), pl(' '), op('='), pl(' '), num('0')],
  [pl('        '), pl('discounts'), pl('['), pl('cat'), pl(']'), pl(' '), op('+='), pl(' '), pl('disc')],
  [pl('        '), pl('total'), pl(' '), op('+='), pl(' '), pl('item'), pl('.'), pl('price'), pl(' '), op('-'), pl(' '), pl('disc')],
  [pl('    '), cmt('# TODO: refactor tax calculation')],
  [pl('    '), pl('tax_rate'), pl(' '), op('='), pl(' '), pl('ctx'), pl('.'), fn('get_tax_rate'), pl('('), pl('order'), pl('.'), pl('region'), pl(')')],
  [pl('    '), kw('if'), pl(' '), pl('tax_rate'), pl(' '), kw('is'), pl(' '), kw('None'), pl(':')],
  [pl('        '), pl('tax_rate'), pl(' '), op('='), pl(' '), num('0.08')],
  [pl('    '), pl('tax'), pl(' '), op('='), pl(' '), pl('total'), pl(' '), op('*'), pl(' '), pl('tax_rate')],
  [pl('    '), cmt('# PATCH: apply loyalty credit')],
  [pl('    '), pl('credit'), pl(' '), op('='), pl(' '), blt('min'), pl('(')],
  [pl('        '), pl('ctx'), pl('.'), fn('get_loyalty_credit'), pl('('), pl('order'), pl('.'), pl('customer_id'), pl('),')],
  [pl('        '), pl('total'), pl(' '), op('*'), pl(' '), num('0.2')],
  [pl('    '), pl(')')],
  [pl('    '), pl('final'), pl(' '), op('='), pl(' '), pl('total'), pl(' '), op('+'), pl(' '), pl('tax'), pl(' '), op('-'), pl(' '), pl('credit')],
  [pl('    '), cmt('# TODO: add audit logging')],
  [pl('    '), pl('result'), pl(' '), op('='), pl(' '), blt('dict'), pl('(')],
  [pl('        '), pl('subtotal'), op('='), pl('total'), pl(',')],
  [pl('        '), pl('tax'), op('='), pl('tax'), pl(',')],
  [pl('        '), pl('credit'), op('='), pl('credit'), pl(',')],
  [pl('        '), pl('total'), op('='), pl('final'), pl(',')],
  [pl('    '), pl(')')],
  [pl('    '), kw('return'), pl(' '), pl('result')],
];

// === Regenerated (clean) code — 30 lines, no patches or TODOs ===
export const CLEAN_CODE: CodeLine[] = [
  [kw('def'), pl(' '), fn('process_order'), pl('('), param('order'), pl(', '), param('ctx'), pl('):')],
  [pl('    '), pl('order'), pl('.'), fn('validate'), pl('()')],
  [pl('')],
  [pl('    '), pl('pricing'), pl(' '), op('='), pl(' '), fn('calculate_pricing'), pl('('), pl('order'), pl('.'), pl('items'), pl(')')],
  [pl('    '), pl('tax'), pl(' '), op('='), pl(' '), fn('compute_tax'), pl('('), pl('pricing'), pl('.'), pl('subtotal'), pl(', '), pl('order'), pl('.'), pl('region'), pl(', '), pl('ctx'), pl(')')],
  [pl('    '), pl('credit'), pl(' '), op('='), pl(' '), fn('apply_loyalty'), pl('('), pl('order'), pl('.'), pl('customer_id'), pl(', '), pl('pricing'), pl('.'), pl('subtotal'), pl(', '), pl('ctx'), pl(')')],
  [pl('')],
  [pl('    '), kw('return'), pl(' '), fn('OrderResult'), pl('(')],
  [pl('        '), pl('subtotal'), op('='), pl('pricing'), pl('.'), pl('subtotal'), pl(',')],
  [pl('        '), pl('discounts'), op('='), pl('pricing'), pl('.'), pl('discounts'), pl(',')],
  [pl('        '), pl('tax'), op('='), pl('tax'), pl(',')],
  [pl('        '), pl('credit'), op('='), pl('credit'), pl(',')],
  [pl('        '), pl('total'), op('='), pl('pricing'), pl('.'), pl('subtotal'), pl(' '), op('+'), pl(' '), pl('tax'), pl(' '), op('-'), pl(' '), pl('credit'), pl(',')],
  [pl('    '), pl(')')],
  [pl('')],
  [pl('')],
  [kw('def'), pl(' '), fn('calculate_pricing'), pl('('), param('items'), pl('):')],
  [pl('    '), pl('subtotal'), pl(' '), op('='), pl(' '), num('0')],
  [pl('    '), pl('discounts'), pl(' '), op('='), pl(' '), blt('defaultdict'), pl('('), blt('float'), pl(')')],
  [pl('')],
  [pl('    '), kw('for'), pl(' '), pl('item'), pl(' '), kw('in'), pl(' '), pl('items'), pl(':')],
  [pl('        '), pl('disc'), pl(' '), op('='), pl(' '), pl('DISCOUNT_RATES'), pl('.'), fn('get'), pl('('), pl('item'), pl('.'), pl('discount_type'), pl(', '), num('0'), pl(')'), pl(' '), op('*'), pl(' '), pl('item'), pl('.'), pl('price')],
  [pl('        '), pl('discounts'), pl('['), pl('item'), pl('.'), pl('category'), pl(']'), pl(' '), op('+='), pl(' '), pl('disc')],
  [pl('        '), pl('subtotal'), pl(' '), op('+='), pl(' '), pl('item'), pl('.'), pl('price'), pl(' '), op('-'), pl(' '), pl('disc')],
  [pl('')],
  [pl('    '), kw('return'), pl(' '), fn('PricingResult'), pl('('), pl('subtotal'), op('='), pl('subtotal'), pl(', '), pl('discounts'), op('='), blt('dict'), pl('('), pl('discounts'), pl(')'), pl(')')],
  [pl('')],
  [pl('')],
  [kw('def'), pl(' '), fn('compute_tax'), pl('('), param('subtotal'), pl(', '), param('region'), pl(', '), param('ctx'), pl('):')],
  [pl('    '), kw('return'), pl(' '), pl('subtotal'), pl(' '), op('*'), pl(' '), pl('('), pl('ctx'), pl('.'), fn('get_tax_rate'), pl('('), pl('region'), pl(')'), pl(' '), kw('or'), pl(' '), num('0.08'), pl(')')],
];
