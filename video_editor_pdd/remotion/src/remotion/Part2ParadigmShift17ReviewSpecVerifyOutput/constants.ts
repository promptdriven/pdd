// ─── Colors ──────────────────────────────────────────────────────────────────
export const BG_COLOR = '#0A0F1A';
export const PANEL_BG = '#1E293B';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.03;

export const TEXT_PRIMARY = '#E2E8F0';
export const AMBER_ACCENT = '#D9944A';
export const GREEN_ACCENT = '#5AAA6E';

// ─── Dimensions ──────────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 360;

export const PANEL_BORDER_RADIUS = 8;
export const PANEL_PADDING = 24;

// ─── Layout positions ────────────────────────────────────────────────────────
export const PROMPT_X = 200;
export const PROMPT_Y = 200;
export const PROMPT_WIDTH = 650;

export const TESTS_X = 1050;
export const TESTS_Y = 200;
export const TESTS_WIDTH = 650;

export const LABEL_Y = 850;
export const UNDERLINE_Y = 880;

// ─── Grid ────────────────────────────────────────────────────────────────────
export const GRID_SPACING = 60;

// ─── Animation frames ────────────────────────────────────────────────────────
export const DISSOLVE_START = 0;
export const DISSOLVE_END = 45;

export const PROMPT_FADE_START = 45;
export const PROMPT_FADE_DURATION = 30;

export const TESTS_FADE_START = 105;
export const TESTS_FADE_DURATION = 30;
export const TEST_ROW_STAGGER = 12; // frames between each test row appearing

export const LABEL_START = 180;
export const LABEL_CHAR_DELAY = 2; // frames per character
export const UNDERLINE_START = 220; // label start + ~40 frames
export const UNDERLINE_DURATION = 20;

export const MORPH_START = 240;
export const MORPH_DURATION = 90; // frames 240–330
export const HOLD_START = 330;

// ─── Aura ────────────────────────────────────────────────────────────────────
export const AURA_BLUR = 20;
export const AURA_OPACITY = 0.15;

// ─── Prompt lines (inline data) ──────────────────────────────────────────────
export const PROMPT_LINES: string[] = [
  '# Counter Module Specification',
  '',
  'Build a counter module with the following behavior:',
  '',
  '1. Expose an `increment()` method that adds 1',
  '   to the internal count.',
  '2. Expose a `reset()` method that sets count to 0.',
  '3. On overflow past MAX_INT, wrap to 0.',
  '4. Handle the edge case where count is already 0',
  '   and reset is called (no-op).',
  '5. Support concurrent access — increment must be',
  '   atomic across threads.',
  '',
  '## Constraints',
  '- Language: TypeScript',
  '- No external dependencies',
  '- 100% test coverage required',
  '',
  '## Output',
  'Return the module and a matching test suite.',
];

// ─── Test data ───────────────────────────────────────────────────────────────
export interface TestRow {
  name: string;
  status: 'pass';
}

export const TEST_ROWS: TestRow[] = [
  { name: 'test_counter_increments', status: 'pass' },
  { name: 'test_reset_clears_state', status: 'pass' },
  { name: 'test_overflow_wraps', status: 'pass' },
  { name: 'test_edge_case_zero', status: 'pass' },
  { name: 'test_concurrent_access', status: 'pass' },
];

// ─── Label text ──────────────────────────────────────────────────────────────
export const LABEL_TEXT = 'Review the spec. Verify the output.';

// ─── Code-diff lines (for dissolve effect) ───────────────────────────────────
export const DIFF_LINES: string[] = [
  '- function process(data) {',
  '+   const result = transform(data);',
  '-   if (result.error) {',
  '+     throw new Error(result.message);',
  '    }',
  '-   return result.value;',
  '+ }',
  '  ',
  '- module.exports = { process };',
  '+ export default process;',
  '-   const old = require("./legacy");',
  '+   import { modern } from "./modern";',
];
