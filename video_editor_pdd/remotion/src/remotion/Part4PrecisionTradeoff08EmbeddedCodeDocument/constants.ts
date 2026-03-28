// === Colors ===
export const BG_CANVAS = '#0A0F1A';
export const DOC_BG = '#0F172A';
export const DOC_BORDER = '#1E293B';
export const CODE_BG = '#111827';
export const CODE_BORDER = '#334155';
export const CODE_ACCENT = '#64748B';
export const CODE_TEXT_COLOR = '#A5F3FC';
export const HEADING_COLOR = '#E2E8F0';
export const PROSE_COLOR = '#CBD5E1';
export const ANNOTATION_PROSE_COLOR = '#D9944A';
export const ANNOTATION_CODE_COLOR = '#4A90D9';
export const BOTTOM_LABEL_COLOR = '#94A3B8';
export const CODE_GLOW_COLOR = '#4A90D9';

// === Dimensions ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const DOC_WIDTH = 1000;
export const DOC_HEIGHT = 720;
export const DOC_X = (CANVAS_WIDTH - DOC_WIDTH) / 2; // 460
export const DOC_Y = 140;
export const DOC_PADDING = 48;
export const DOC_BORDER_RADIUS = 12;
export const CODE_BORDER_RADIUS = 6;
export const CODE_ACCENT_WIDTH = 3;

// === Typography ===
export const HEADING_SIZE = 20;
export const PROSE_SIZE = 15;
export const CODE_SIZE = 13;
export const ANNOTATION_SIZE = 13;
export const BOTTOM_LABEL_SIZE = 18;
export const PROSE_LINE_HEIGHT = 1.6;
export const PARAGRAPH_SPACING = 20;

// === Animation Frames ===
export const TOTAL_FRAMES = 840;
export const FPS = 30;

// Document fade-in
export const DOC_FADE_START = 0;
export const DOC_FADE_DURATION = 30;

// Text reveal
export const TEXT_REVEAL_START = 30;
export const TEXT_LINE_RATE = 8; // frames per line

// Code block appear
export const CODE_APPEAR_START = 180;
export const CODE_APPEAR_DURATION = 20;
export const CODE_GLOW_DURATION = 15;

// Below-code prose
export const BELOW_CODE_START = 300;

// Annotations
export const ANNOTATIONS_START = 300;
export const ANNOTATION_DRAW_DURATION = 20;

// Bottom label
export const BOTTOM_LABEL_START = 420;
export const BOTTOM_LABEL_FADE_DURATION = 20;

// Fade out
export const FADE_OUT_START = 780;
export const FADE_OUT_DURATION = 60;

// === Document Content ===
export const DOC_HEADING = '## Parser Module';

export const PROSE_ABOVE_CODE = [
  'Parse incoming JSON payloads according to the defined',
  'schema. Validate required fields, check type constraints,',
  'and normalize nested structures before processing.',
  '',
  'Handle malformed input by returning structured errors',
  'with descriptive messages and field-level context.',
  'Support nested objects up to 5 levels deep.',
  '',
];

export const EMBEDDED_CODE = [
  'def compare_priority(a: Task, b: Task) -> int:',
  '    """Strict ordering for priority queue insertion."""',
  '    if a.deadline != b.deadline:',
  '        return -1 if a.deadline < b.deadline else 1',
  '    if a.weight != b.weight:',
  '        return -1 if a.weight > b.weight else 1',
  '    # Tiebreak: lower ID = older task = higher priority',
  '    return -1 if a.id < b.id else (0 if a.id == b.id else 1)',
];

export const PROSE_BELOW_CODE = [
  'For all other formatting, follow standard conventions.',
  'Return values should use the unified response envelope.',
  'Log structured metadata for every processed payload.',
];

export const BOTTOM_LABEL_TEXT = 'The boundary between prompt and code is fluid.';
