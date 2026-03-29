// === Colors ===
export const BG_COLOR = '#0A0F1A';
export const AMBER_ACCENT = '#D9944A';
export const BLUE_ACCENT = '#4A90D9';
export const ARROW_COLOR = '#64748B';
export const CODE_BG = '#1E293B';
export const CODE_GLOW = '#5AAA6E';
export const CODE_TEXT_COLOR = '#CBD5E1';
export const LABEL_MUTED = '#94A3B8';

// === Canvas ===
export const WIDTH = 1920;
export const HEIGHT = 1080;

// === Layout ===
export const LEFT_COL_X = 80;
export const RIGHT_COL_X = 1040;
export const COL_WIDTH = 800;
export const CENTER_GAP = 40;

// Left column prompt file
export const LEFT_PROMPT_X = 240;
export const LEFT_PROMPT_Y = 100;
export const LEFT_PROMPT_W = 320;
export const LEFT_PROMPT_H = 180;

// Right column prompt file
export const RIGHT_PROMPT_X = 1360;
export const RIGHT_PROMPT_Y = 130;
export const RIGHT_PROMPT_W = 200;
export const RIGHT_PROMPT_H = 120;

// Code blocks
export const CODE_BLOCK_W = 320;
export const CODE_BLOCK_H = 260;
export const LEFT_CODE_X = 240;
export const LEFT_CODE_Y = 380;
export const RIGHT_CODE_X = 1300;
export const RIGHT_CODE_Y = 380;

// Arrows
export const ARROW_LENGTH = 40;
export const LEFT_ARROW_X = 400;
export const LEFT_ARROW_TOP = 300;
export const RIGHT_ARROW_X = 1460;
export const RIGHT_ARROW_TOP = 270;

// Labels
export const LEFT_LABEL_X = 400;
export const LEFT_LABEL_Y = 670;
export const RIGHT_LABEL_X = 1460;
export const RIGHT_LABEL_Y = 670;

// Comparison bar
export const BAR_Y = 950;
export const BAR_WIDTH = 800;
export const BAR_CENTER_X = WIDTH / 2;
export const BAR_LEFT_WIDTH = 500; // proportional to 50 lines
export const BAR_RIGHT_WIDTH = 100; // proportional to 10 lines

// === Animation Frames ===
export const TOTAL_FRAMES = 240;

// Phase 1: Prompts appear (0-45)
export const PROMPT_APPEAR_START = 0;
export const PROMPT_APPEAR_END = 45;
export const PROMPT_FADE_DURATION = 30;

// Phase 2: Arrows draw (45-90)
export const ARROW_DRAW_START = 45;
export const ARROW_DRAW_END = 90;
export const ARROW_DRAW_DURATION = 20;

// Phase 3: Code blocks generate (90-150)
export const CODE_GEN_START = 90;
export const CODE_GEN_END = 150;
export const CODE_LINE_RATE = 4; // 1 line per 4 frames
export const CODE_GLOW_DURATION = 15;

// Phase 4: Labels appear (150-195)
export const LABEL_APPEAR_START = 150;
export const LABEL_APPEAR_END = 195;
export const LABEL_FADE_DURATION = 20;

// Phase 5: Comparison bar (195-210)
export const BAR_APPEAR_START = 195;
export const BAR_APPEAR_END = 210;
export const BAR_ANIM_DURATION = 20;

// Phase 6: Hold + Fade out (210-240)
export const FADEOUT_START = 210;
export const FADEOUT_DURATION = 30;

// === Test indicators ===
export const TEST_COUNT = 47;
export const TEST_DOT_SIZE = 5;

// === Typography ===
export const FONT_INTER = 'Inter, sans-serif';
export const FONT_MONO = 'JetBrains Mono, monospace';

// === Generated code lines (shared between both blocks) ===
export const GENERATED_CODE_LINES = [
  'export function validateSchema(input: Record<string, unknown>) {',
  '  const errors: string[] = [];',
  '  const required = ["id", "name", "type", "status"];',
  '',
  '  for (const field of required) {',
  '    if (!(field in input)) {',
  '      errors.push(`Missing required field: ${field}`);',
  '    }',
  '  }',
  '',
  '  if (typeof input.id !== "string" || input.id.length === 0) {',
  '    errors.push("id must be a non-empty string");',
  '  }',
  '',
  '  return { valid: errors.length === 0, errors };',
  '}',
];
