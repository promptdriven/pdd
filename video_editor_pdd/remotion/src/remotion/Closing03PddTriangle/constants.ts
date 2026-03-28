// ── Canvas ──
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const BACKGROUND_COLOR = '#0A0F1A';
export const GRID_SPACING = 60;
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.03;

// ── Triangle Geometry ──
export const TRIANGLE_CENTER_X = 960;
export const TRIANGLE_CENTER_Y = 500;

export interface Vertex {
  label: string;
  x: number;
  y: number;
  color: string;
}

export const VERTICES: Vertex[] = [
  { label: 'PROMPT', x: 960, y: 180, color: '#D9944A' },
  { label: 'TESTS', x: 683, y: 680, color: '#4AD9A0' },
  { label: 'GROUNDING', x: 1237, y: 680, color: '#4A90D9' },
];

export const VERTEX_DOT_RADIUS = 12;
export const VERTEX_GLOW_RADIUS = 60;
export const VERTEX_GLOW_OPACITY = 0.25;

// ── Triangle Edges ──
export const EDGE_WIDTH = 2;
export const EDGE_COLOR = '#334155';
export const EDGE_OPACITY = 0.6;

// ── Label Typography ──
export const LABEL_FONT_SIZE = 24;
export const LABEL_FONT_FAMILY = 'Inter, sans-serif';
export const LABEL_FONT_WEIGHT = 700;
export const LABEL_OFFSET_Y = -30; // offset above/below vertex

// ── Center Code Block ──
export const CODE_BOX_WIDTH = 280;
export const CODE_BOX_HEIGHT = 160;
export const CODE_BOX_X = TRIANGLE_CENTER_X - CODE_BOX_WIDTH / 2;
export const CODE_BOX_Y = 480 - CODE_BOX_HEIGHT / 2;
export const CODE_BG_COLOR = '#111827';
export const CODE_BG_OPACITY = 0.8;
export const CODE_BORDER_RADIUS = 8;
export const CODE_FONT_SIZE = 13;
export const CODE_FONT_FAMILY = 'JetBrains Mono, monospace';

// ── Syntax Colors ──
export const SYNTAX_KEYWORD = '#C084FC';
export const SYNTAX_STRING = '#86EFAC';
export const SYNTAX_FUNCTION = '#93C5FD';
export const SYNTAX_PUNCTUATION = '#94A3B8';
export const SYNTAX_DEFAULT = '#E2E8F0';

// ── Code Lines ──
export const CODE_LINES: string[] = [
  'def calculate_total(items):',
  '    return sum(i.price for i in items)',
  '',
  'def apply_discount(total, pct):',
  '    return total * (1 - pct)',
];

// ── Animation Timing (frames) ──
export const VERTEX_TOP_START = 0;
export const VERTEX_TOP_END = 20;
export const VERTEX_LEFT_START = 20;
export const VERTEX_LEFT_END = 40;
export const VERTEX_RIGHT_START = 40;
export const VERTEX_RIGHT_END = 60;

export const EDGES_START = 50;
export const EDGE_DURATION = 10; // each edge draws over ~10 frames
export const EDGES_TOTAL_DURATION = 30;

export const CODE_FADE_START = 80;
export const CODE_TYPE_START = 80;
export const CODE_TYPE_END = 130;
export const CHARS_PER_FRAME = 0.5; // 1 char every 2 frames

export const PULSE_START = 130;
export const PULSE_CYCLE_FRAMES = 60;

// ── Total Duration ──
export const DURATION_FRAMES = 180;
export const FPS = 30;
