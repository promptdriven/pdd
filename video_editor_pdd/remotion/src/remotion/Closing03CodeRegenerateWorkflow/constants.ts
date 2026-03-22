// ─── Colors ───
export const BG_COLOR = '#0A1628';
export const PANEL_BG = '#1E293B';
export const TERMINAL_BG = '#0F172A';
export const TEXT_DEFAULT = '#E2E8F0';
export const TEXT_DIM = '#94A3B8';
export const HEADER_COLOR = '#64748B';
export const KEYWORD_BLUE = '#4A90D9';
export const STRING_GREEN = '#5AAA6E';
export const BUG_RED = '#EF4444';
export const PASS_GREEN = '#22C55E';
export const TEST_GREEN = '#5AAA6E';
export const AMBER_HIGHLIGHT = '#D9944A';
export const ACCENT_BLUE = '#3B82F6';
export const ANNOTATION_UNDERLINE = '#4A90D9';

// ─── Layout ───
export const CANVAS_W = 1920;
export const CANVAS_H = 1080;

export const CODE_PANEL_X = 60;
export const CODE_PANEL_Y = 80;
export const CODE_PANEL_W = 860;
export const CODE_PANEL_H = 700;

export const TEST_PANEL_X = 940;
export const TEST_PANEL_Y = 80;
export const TEST_PANEL_W = 920;
export const TEST_PANEL_H = 700;

export const TERMINAL_X = 60;
export const TERMINAL_Y = 820;
export const TERMINAL_W = 1800;
export const TERMINAL_H = 200;

// ─── Typography ───
export const MONO_FONT = 'JetBrains Mono, Menlo, Consolas, monospace';
export const SANS_FONT = 'Inter, system-ui, sans-serif';

// ─── Frame timings ───
export const TOTAL_FRAMES = 300;
export const LAYOUT_FADEIN_END = 20;
export const CMD1_START = 30;
export const CMD1_TEXT = 'pdd bug user_parser';
export const CMD1_OUTPUT = 'Creating failing test...';
export const NEW_TEST_APPEAR = 50;
export const CMD2_START = 70;
export const CMD2_TEXT = 'pdd fix user_parser';
export const CMD2_OUTPUT = 'Regenerating...';
export const DISSOLVE_START = 100;
export const DISSOLVE_END = 130;
export const STREAM_START = 130;
export const STREAM_END = 160;
export const TESTS_PASS_FRAME = 160;
export const ANNOTATION_START = 200;
export const ANNOTATION_DURATION = 18;

// ─── Original (buggy) code lines ───
export interface CodeToken {
  text: string;
  color: string;
}

export const ORIGINAL_CODE: CodeToken[][] = [
  [{ text: 'import', color: KEYWORD_BLUE }, { text: ' re', color: TEXT_DEFAULT }],
  [{ text: 'from', color: KEYWORD_BLUE }, { text: ' typing ', color: TEXT_DEFAULT }, { text: 'import', color: KEYWORD_BLUE }, { text: ' Optional', color: TEXT_DEFAULT }],
  [{ text: '', color: TEXT_DEFAULT }],
  [{ text: 'class', color: KEYWORD_BLUE }, { text: ' UserParser:', color: TEXT_DEFAULT }],
  [{ text: '    ', color: TEXT_DEFAULT }, { text: 'def', color: KEYWORD_BLUE }, { text: ' __init__', color: TEXT_DEFAULT }, { text: '(self):', color: TEXT_DEFAULT }],
  [{ text: '        self.pattern = re.compile(', color: TEXT_DEFAULT }, { text: 'r"[\\w.]+"', color: STRING_GREEN }, { text: ')', color: TEXT_DEFAULT }],
  [{ text: '        self.cache = {}', color: TEXT_DEFAULT }],
  [{ text: '', color: TEXT_DEFAULT }],
  [{ text: '    ', color: TEXT_DEFAULT }, { text: 'def', color: KEYWORD_BLUE }, { text: ' parse(self, raw: str) -> Optional[dict]:', color: TEXT_DEFAULT }],
  [{ text: '        ', color: TEXT_DEFAULT }, { text: 'if not', color: KEYWORD_BLUE }, { text: ' raw:', color: TEXT_DEFAULT }],
  [{ text: '            ', color: TEXT_DEFAULT }, { text: 'return', color: KEYWORD_BLUE }, { text: ' None', color: KEYWORD_BLUE }],
  [{ text: '        name = raw.split(', color: TEXT_DEFAULT }, { text: '"\\x00"', color: STRING_GREEN }, { text: ')[0]  # BUG: no sanitize', color: BUG_RED }],
  [{ text: '        email = self.pattern.findall(raw)', color: TEXT_DEFAULT }],
  [{ text: '        ', color: TEXT_DEFAULT }, { text: 'return', color: KEYWORD_BLUE }, { text: ' {', color: TEXT_DEFAULT }],
  [{ text: '            ', color: TEXT_DEFAULT }, { text: '"name"', color: STRING_GREEN }, { text: ': name,', color: TEXT_DEFAULT }],
  [{ text: '            ', color: TEXT_DEFAULT }, { text: '"email"', color: STRING_GREEN }, { text: ': email[0] ', color: TEXT_DEFAULT }, { text: 'if', color: KEYWORD_BLUE }, { text: ' email ', color: TEXT_DEFAULT }, { text: 'else', color: KEYWORD_BLUE }, { text: ' None,', color: TEXT_DEFAULT }],
  [{ text: '        }', color: TEXT_DEFAULT }],
  [{ text: '', color: TEXT_DEFAULT }],
  [{ text: '    ', color: TEXT_DEFAULT }, { text: 'def', color: KEYWORD_BLUE }, { text: ' validate(self, data: dict) -> bool:', color: TEXT_DEFAULT }],
  [{ text: '        ', color: TEXT_DEFAULT }, { text: 'return', color: KEYWORD_BLUE }, { text: ' bool(data.get(', color: TEXT_DEFAULT }, { text: '"name"', color: STRING_GREEN }, { text: '))', color: TEXT_DEFAULT }],
];

// ─── Regenerated (fixed) code lines ───
export const REGENERATED_CODE: CodeToken[][] = [
  [{ text: 'import', color: KEYWORD_BLUE }, { text: ' re', color: TEXT_DEFAULT }],
  [{ text: 'from', color: KEYWORD_BLUE }, { text: ' typing ', color: TEXT_DEFAULT }, { text: 'import', color: KEYWORD_BLUE }, { text: ' Optional', color: TEXT_DEFAULT }],
  [{ text: '', color: TEXT_DEFAULT }],
  [{ text: 'class', color: KEYWORD_BLUE }, { text: ' UserParser:', color: TEXT_DEFAULT }],
  [{ text: '    ', color: TEXT_DEFAULT }, { text: 'def', color: KEYWORD_BLUE }, { text: ' __init__', color: TEXT_DEFAULT }, { text: '(self):', color: TEXT_DEFAULT }],
  [{ text: '        self._pattern = re.compile(', color: TEXT_DEFAULT }, { text: 'r"[\\w.]+"', color: STRING_GREEN }, { text: ')', color: TEXT_DEFAULT }],
  [{ text: '        self._store: dict = {}', color: TEXT_DEFAULT }],
  [{ text: '', color: TEXT_DEFAULT }],
  [{ text: '    ', color: TEXT_DEFAULT }, { text: 'def', color: KEYWORD_BLUE }, { text: ' parse(self, raw: str) -> Optional[dict]:', color: TEXT_DEFAULT }],
  [{ text: '        ', color: TEXT_DEFAULT }, { text: 'if not', color: KEYWORD_BLUE }, { text: ' raw:', color: TEXT_DEFAULT }],
  [{ text: '            ', color: TEXT_DEFAULT }, { text: 'return', color: KEYWORD_BLUE }, { text: ' None', color: KEYWORD_BLUE }],
  [{ text: '        sanitized = raw.replace(', color: TEXT_DEFAULT }, { text: '"\\x00"', color: STRING_GREEN }, { text: ', ', color: TEXT_DEFAULT }, { text: '""', color: STRING_GREEN }, { text: ')', color: TEXT_DEFAULT }],
  [{ text: '        user_name = sanitized.strip()', color: TEXT_DEFAULT }],
  [{ text: '        matches = self._pattern.findall(sanitized)', color: TEXT_DEFAULT }],
  [{ text: '        ', color: TEXT_DEFAULT }, { text: 'return', color: KEYWORD_BLUE }, { text: ' {', color: TEXT_DEFAULT }],
  [{ text: '            ', color: TEXT_DEFAULT }, { text: '"name"', color: STRING_GREEN }, { text: ': user_name,', color: TEXT_DEFAULT }],
  [{ text: '            ', color: TEXT_DEFAULT }, { text: '"email"', color: STRING_GREEN }, { text: ': matches[0] ', color: TEXT_DEFAULT }, { text: 'if', color: KEYWORD_BLUE }, { text: ' matches ', color: TEXT_DEFAULT }, { text: 'else', color: KEYWORD_BLUE }, { text: ' None,', color: TEXT_DEFAULT }],
  [{ text: '        }', color: TEXT_DEFAULT }],
  [{ text: '', color: TEXT_DEFAULT }],
  [{ text: '    ', color: TEXT_DEFAULT }, { text: 'def', color: KEYWORD_BLUE }, { text: ' validate(self, entry: dict) -> bool:', color: TEXT_DEFAULT }],
  [{ text: '        ', color: TEXT_DEFAULT }, { text: 'return', color: KEYWORD_BLUE }, { text: ' bool(entry.get(', color: TEXT_DEFAULT }, { text: '"name"', color: STRING_GREEN }, { text: '))', color: TEXT_DEFAULT }],
];

// ─── Test data ───
export const EXISTING_TESTS = [
  'test_basic_parse',
  'test_empty_input',
  'test_unicode_name',
  'test_max_length',
];

export const NEW_TEST = 'test_null_injection';

// ─── Bug line index (0-based) ───
export const BUG_LINE_INDEX = 11;
