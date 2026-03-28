// ── Canvas ──────────────────────────────────────────────────────────
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const FPS = 30;
export const DURATION_FRAMES = 240;

// ── Colors ─────────────────────────────────────────────────────────
export const BG_COLOR = '#0A0F1A';
export const EDITOR_FRAME_COLOR = '#1E293B';
export const TITLE_BAR_COLOR = '#151B28';
export const FILENAME_COLOR = '#E2E8F0';
export const TEXT_COLOR = '#CBD5E1';
export const LINE_NUMBER_COLOR = '#64748B';
export const ACCENT_AMBER = '#D9944A';
export const TRAFFIC_RED = '#FF5F57';
export const TRAFFIC_YELLOW = '#FEBC2E';
export const TRAFFIC_GREEN = '#28C840';

// ── Editor Dimensions ──────────────────────────────────────────────
export const EDITOR_WIDTH = 1200;
export const EDITOR_HEIGHT = 700;
export const EDITOR_X = (CANVAS_WIDTH - EDITOR_WIDTH) / 2; // 360
export const EDITOR_Y = 160;
export const EDITOR_BORDER_RADIUS = 8;
export const TITLE_BAR_HEIGHT = 36;
export const GUTTER_WIDTH = 48;
export const GUTTER_INDICATOR_WIDTH = 3;
export const LINE_HEIGHT = 22;

// ── Animation Timing ───────────────────────────────────────────────
export const WINDOW_FADE_IN_END = 30;
export const BADGE_SCALE_START = 30;
export const BADGE_SCALE_DURATION = 15;
export const CONTENT_REVEAL_START = 30;
export const LINES_PER_FRAME = 1.5;
export const LABEL_FADE_IN_START = 180;
export const LABEL_FADE_IN_DURATION = 20;
export const FINAL_FADE_START = 210;
export const FINAL_FADE_DURATION = 30;

// ── Prompt Line Data ───────────────────────────────────────────────
export interface PromptLineData {
  lineNumber: number;
  text: string;
  section: 'header' | 'spec' | 'edge_case' | 'error' | 'format' | 'perf';
  isHighlight: boolean;
}

function buildLines(): PromptLineData[] {
  const lines: PromptLineData[] = [];

  const content: Array<{
    range: [number, number];
    section: PromptLineData['section'];
    highlight: boolean;
    texts: string[];
  }> = [
    {
      range: [1, 3],
      section: 'header',
      highlight: false,
      texts: [
        '# parser_v1 — Natural-language-to-AST parser module',
        '# Converts free-form user instructions into typed AST nodes.',
        '# Version 1.0 — no test suite available.',
      ],
    },
    {
      range: [4, 12],
      section: 'spec',
      highlight: false,
      texts: [
        '',
        '## Input Format',
        'Accept UTF-8 text, 1–4096 characters inclusive.',
        'Normalize Unicode NFC before processing.',
        'Strip leading/trailing whitespace; collapse internal runs.',
        'If input contains only whitespace, return EmptyInput node.',
        'Reject null bytes — raise InvalidCharError(position).',
        'Support multiline input: split on \\n, process per-line.',
        'Line delimiter may be \\n, \\r\\n, or \\r — normalize to \\n.',
      ],
    },
    {
      range: [13, 22],
      section: 'edge_case',
      highlight: true,
      texts: [
        '',
        '## Edge Cases (MUST handle all)',
        'Nested parentheses up to depth 8 — deeper → DepthError.',
        'Escaped quotes within strings: \\" and \\\' must be preserved.',
        'Empty string literals ("") produce EmptyStringLiteral node.',
        'Consecutive operators (e.g., "++", "--") are INVALID.',
        'Unicode emoji in identifiers → UnsupportedCharWarning.',
        'Mixed tab/space indentation → IndentationWarning, use spaces.',
        'Dangling comma after last element is PERMITTED (trailing).',
        'Zero-width characters (U+200B..U+200D) must be stripped.',
      ],
    },
    {
      range: [23, 35],
      section: 'error',
      highlight: false,
      texts: [
        '',
        '## Error Handling Rules',
        'All errors include: { type, message, position, context }.',
        'Position is { line: number, column: number, offset: number }.',
        'On parse failure, collect ALL errors — do not stop at first.',
        'Maximum 50 errors; beyond that, emit TooManyErrors and halt.',
        'Warnings do not prevent AST generation — attach to node.',
        'Error messages must be human-readable, <120 chars each.',
        'Include 3 chars of surrounding context in error.context.',
        'Recovery strategy: skip to next statement boundary ";".',
        'If no ";" found within 200 chars, skip to next newline.',
        'Fatal errors (stack overflow, OOM) → FatalError, abort.',
        'Log all errors to structured JSON before returning result.',
      ],
    },
    {
      range: [36, 45],
      section: 'format',
      highlight: false,
      texts: [
        '',
        '## Output Format Constraints',
        'Return value: { ast: ASTNode, errors: Error[], meta: Meta }.',
        'ASTNode types: Program, Statement, Expression, Literal, Id.',
        'Each node: { type, children: ASTNode[], span: Span }.',
        'Span: { start: Position, end: Position }.',
        'Meta: { parseTimeMs, inputLength, nodeCount, errorCount }.',
        'JSON output must be deterministic — sorted keys, no undefined.',
        'Maximum AST depth: 64 — deeper structures are flattened.',
        'String values in AST capped at 1024 chars, truncate with …',
      ],
    },
    {
      range: [46, 50],
      section: 'perf',
      highlight: false,
      texts: [
        '',
        '## Performance Requirements',
        'Parse time < 50ms for inputs under 1024 chars.',
        'Memory usage < 10MB for any valid input.',
        'Must handle 100 sequential parse calls without degradation.',
      ],
    },
  ];

  for (const block of content) {
    for (let i = 0; i < block.texts.length; i++) {
      lines.push({
        lineNumber: block.range[0] + i,
        text: block.texts[i],
        section: block.section,
        isHighlight: block.highlight,
      });
    }
  }

  return lines;
}

export const PROMPT_LINES: PromptLineData[] = buildLines();
export const TOTAL_LINES = 50;
