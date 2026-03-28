// ── Colors ──────────────────────────────────────────────────────────
export const BG_COLOR = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.03;
export const GRID_SPACING = 60;

// Code block
export const CODE_BG = '#111827';
export const CODE_BG_OPACITY = 0.85;
export const CODE_BORDER_RADIUS = 8;

// Syntax colors
export const SYNTAX_KEYWORD = '#C084FC';
export const SYNTAX_STRING = '#86EFAC';
export const SYNTAX_FUNCTION = '#93C5FD';
export const SYNTAX_DEFAULT = '#E2E8F0';
export const SYNTAX_COMMENT = '#64748B';

// Terminal
export const TERMINAL_BG = '#000000';
export const TERMINAL_BG_OPACITY = 0.9;
export const TERMINAL_TEXT = '#4AD9A0';
export const TERMINAL_PROMPT_COLOR = '#94A3B8';
export const CHECK_COLOR = '#22C55E';

// Triangle
export const TRIANGLE_PROMPT_COLOR = '#C084FC';
export const TRIANGLE_TESTS_COLOR = '#22C55E';
export const TRIANGLE_GROUNDING_COLOR = '#3B82F6';
export const TRIANGLE_LINE_COLOR = '#475569';

// ── Dimensions ──────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

// Code block bounding box
export const CODE_BLOCK_WIDTH = 320;
export const CODE_BLOCK_HEIGHT = 180;
export const CODE_BLOCK_CENTER_X = 960;
export const CODE_BLOCK_CENTER_Y = 470;

// Terminal strip
export const TERMINAL_WIDTH = 320;
export const TERMINAL_HEIGHT = 36;
export const TERMINAL_CENTER_X = 960;
export const TERMINAL_CENTER_Y = 600;

// Triangle vertices (equilateral, centered at ~960, 540)
export const TRIANGLE_VERTICES = [
  { x: 960, y: 240, label: 'Prompt', color: TRIANGLE_PROMPT_COLOR },
  { x: 710, y: 680, label: 'Tests', color: TRIANGLE_TESTS_COLOR },
  { x: 1210, y: 680, label: 'Grounding', color: TRIANGLE_GROUNDING_COLOR },
] as const;

// ── Timing (frames) ────────────────────────────────────────────────
export const FPS = 30;
export const TOTAL_DURATION = 150;

// Cycle 1
export const C1_HOLD_END = 10;
export const C1_DISSOLVE_START = 10;
export const C1_DISSOLVE_END = 30;
export const C1_REGEN_START = 30;
export const C1_REGEN_END = 50;
export const C1_TERMINAL_START = 50;
export const C1_CHECK_START = 55;
export const C1_END = 65;

// Cycle 2
export const C2_START = 65;
export const C2_DISSOLVE_START = 65;
export const C2_DISSOLVE_END = 85;
export const C2_REGEN_START = 85;
export const C2_REGEN_END = 105;
export const C2_TERMINAL_START = 105;
export const C2_CHECK_START = 110;
export const C2_END = 120;

// Final hold
export const HOLD_START = 120;

// ── Particle config ────────────────────────────────────────────────
export const PARTICLE_SIZE = 4;
export const PARTICLE_MIN_DRIFT = 20;
export const PARTICLE_MAX_DRIFT = 60;
export const PARTICLE_MIN_DURATION = 10;
export const PARTICLE_MAX_DURATION = 20;

// ── Code Variants ──────────────────────────────────────────────────
export interface CodeLine {
  text: string;
}

export const CODE_V1: CodeLine[] = [
  { text: 'def calculate_total(items):' },
  { text: '    return sum(i.price for i in items)' },
  { text: '' },
  { text: 'def apply_discount(total, pct):' },
  { text: '    return total * (1 - pct)' },
];

export const CODE_V2: CodeLine[] = [
  { text: 'def get_total(cart_items):' },
  { text: '    total = 0' },
  { text: '    for item in cart_items:' },
  { text: '        total += item.price' },
  { text: '    return total' },
];

export const CODE_V3: CodeLine[] = [
  { text: 'def compute_sum(products):' },
  { text: '    prices = [p.price for p in products]' },
  { text: '    return functools.reduce(' },
  { text: '        operator.add, prices, 0' },
  { text: '    )' },
];
