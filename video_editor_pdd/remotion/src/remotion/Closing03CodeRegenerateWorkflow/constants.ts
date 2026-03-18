// Colors
export const COLORS = {
  background: '#0A1628',
  panelBg: '#1E293B',
  terminalBg: '#0F172A',
  textDefault: '#E2E8F0',
  textMuted: '#94A3B8',
  textDim: '#64748B',
  keyword: '#4A90D9',
  string: '#5AAA6E',
  green: '#22C55E',
  greenCheck: '#5AAA6E',
  red: '#EF4444',
  amber: '#D9944A',
  blue: '#3B82F6',
  accentBlue: '#4A90D9',
} as const;

// Layout
export const LAYOUT = {
  codePanel: { x: 60, y: 80, width: 860, height: 700 },
  testPanel: { x: 940, y: 80, width: 920, height: 700 },
  terminal: { x: 60, y: 820, width: 1800, height: 200 },
} as const;

// Font families
export const FONTS = {
  mono: 'JetBrains Mono, Menlo, Monaco, Consolas, monospace',
  sans: 'Inter, -apple-system, BlinkMacSystemFont, sans-serif',
} as const;

// Original Python code (with bug on line 12)
export const ORIGINAL_CODE: Array<{ text: string; tokens: Array<{ value: string; color: string }> }> = [
  { text: 'import re', tokens: [{ value: 'import', color: COLORS.keyword }, { value: ' re', color: COLORS.textDefault }] },
  { text: 'from typing import Optional', tokens: [{ value: 'from', color: COLORS.keyword }, { value: ' typing ', color: COLORS.textDefault }, { value: 'import', color: COLORS.keyword }, { value: ' Optional', color: COLORS.textDefault }] },
  { text: '', tokens: [] },
  { text: 'class UserParser:', tokens: [{ value: 'class', color: COLORS.keyword }, { value: ' UserParser:', color: COLORS.textDefault }] },
  { text: '    """Parse user input strings."""', tokens: [{ value: '    ', color: COLORS.textDefault }, { value: '"""Parse user input strings."""', color: COLORS.string }] },
  { text: '', tokens: [] },
  { text: '    def __init__(self, strict=True):', tokens: [{ value: '    ', color: COLORS.textDefault }, { value: 'def', color: COLORS.keyword }, { value: ' __init__(self, strict=', color: COLORS.textDefault }, { value: 'True', color: COLORS.keyword }, { value: '):', color: COLORS.textDefault }] },
  { text: '        self.strict = strict', tokens: [{ value: '        self.strict = strict', color: COLORS.textDefault }] },
  { text: '        self.pattern = re.compile(r"\\w+")', tokens: [{ value: '        self.pattern = re.compile(r', color: COLORS.textDefault }, { value: '"\\\\w+"', color: COLORS.string }, { value: ')', color: COLORS.textDefault }] },
  { text: '', tokens: [] },
  { text: '    def parse(self, raw: str) -> Optional[dict]:', tokens: [{ value: '    ', color: COLORS.textDefault }, { value: 'def', color: COLORS.keyword }, { value: ' parse(self, raw: str) -> Optional[dict]:', color: COLORS.textDefault }] },
  { text: '        name = raw.split("|")[0]  # BUG: no sanitization', tokens: [{ value: '        name = raw.split(', color: COLORS.textDefault }, { value: '"|"', color: COLORS.string }, { value: ')[0]  ', color: COLORS.textDefault }, { value: '# BUG: no sanitization', color: COLORS.textDim }] },
  { text: '        return {"name": name, "valid": True}', tokens: [{ value: '        ', color: COLORS.textDefault }, { value: 'return', color: COLORS.keyword }, { value: ' {', color: COLORS.textDefault }, { value: '"name"', color: COLORS.string }, { value: ': name, ', color: COLORS.textDefault }, { value: '"valid"', color: COLORS.string }, { value: ': ', color: COLORS.textDefault }, { value: 'True', color: COLORS.keyword }, { value: '}', color: COLORS.textDefault }] },
  { text: '', tokens: [] },
  { text: '    def validate(self, data: dict) -> bool:', tokens: [{ value: '    ', color: COLORS.textDefault }, { value: 'def', color: COLORS.keyword }, { value: ' validate(self, data: dict) -> bool:', color: COLORS.textDefault }] },
  { text: '        if not data.get("name"):', tokens: [{ value: '        ', color: COLORS.textDefault }, { value: 'if', color: COLORS.keyword }, { value: ' ', color: COLORS.textDefault }, { value: 'not', color: COLORS.keyword }, { value: ' data.get(', color: COLORS.textDefault }, { value: '"name"', color: COLORS.string }, { value: '):', color: COLORS.textDefault }] },
  { text: '            return False', tokens: [{ value: '            ', color: COLORS.textDefault }, { value: 'return', color: COLORS.keyword }, { value: ' ', color: COLORS.textDefault }, { value: 'False', color: COLORS.keyword }] },
  { text: '        return len(data["name"]) <= 255', tokens: [{ value: '        ', color: COLORS.textDefault }, { value: 'return', color: COLORS.keyword }, { value: ' len(data[', color: COLORS.textDefault }, { value: '"name"', color: COLORS.string }, { value: ']) <= 255', color: COLORS.textDefault }] },
];

// Bug line index (0-based)
export const BUG_LINE_INDEX = 11;

// Regenerated Python code (clean, different variable names)
export const REGENERATED_CODE: Array<{ text: string; tokens: Array<{ value: string; color: string }> }> = [
  { text: 'import re', tokens: [{ value: 'import', color: COLORS.keyword }, { value: ' re', color: COLORS.textDefault }] },
  { text: 'from typing import Optional', tokens: [{ value: 'from', color: COLORS.keyword }, { value: ' typing ', color: COLORS.textDefault }, { value: 'import', color: COLORS.keyword }, { value: ' Optional', color: COLORS.textDefault }] },
  { text: '', tokens: [] },
  { text: 'class UserParser:', tokens: [{ value: 'class', color: COLORS.keyword }, { value: ' UserParser:', color: COLORS.textDefault }] },
  { text: '    """Safely parse and validate user input."""', tokens: [{ value: '    ', color: COLORS.textDefault }, { value: '"""Safely parse and validate user input."""', color: COLORS.string }] },
  { text: '', tokens: [] },
  { text: '    SAFE_PATTERN = re.compile(r"^[\\w\\s.-]+$")', tokens: [{ value: '    SAFE_PATTERN = re.compile(r', color: COLORS.textDefault }, { value: '"^[\\\\w\\\\s.-]+$"', color: COLORS.string }, { value: ')', color: COLORS.textDefault }] },
  { text: '', tokens: [] },
  { text: '    def __init__(self, strict_mode=True):', tokens: [{ value: '    ', color: COLORS.textDefault }, { value: 'def', color: COLORS.keyword }, { value: ' __init__(self, strict_mode=', color: COLORS.textDefault }, { value: 'True', color: COLORS.keyword }, { value: '):', color: COLORS.textDefault }] },
  { text: '        self.strict_mode = strict_mode', tokens: [{ value: '        self.strict_mode = strict_mode', color: COLORS.textDefault }] },
  { text: '', tokens: [] },
  { text: '    def parse(self, raw_input: str) -> Optional[dict]:', tokens: [{ value: '    ', color: COLORS.textDefault }, { value: 'def', color: COLORS.keyword }, { value: ' parse(self, raw_input: str) -> Optional[dict]:', color: COLORS.textDefault }] },
  { text: '        sanitized = re.sub(r"[^\\w\\s.-]", "", raw_input)', tokens: [{ value: '        sanitized = re.sub(r', color: COLORS.textDefault }, { value: '"[^\\\\w\\\\s.-]"', color: COLORS.string }, { value: ', ', color: COLORS.textDefault }, { value: '""', color: COLORS.string }, { value: ', raw_input)', color: COLORS.textDefault }] },
  { text: '        if not self.SAFE_PATTERN.match(sanitized):', tokens: [{ value: '        ', color: COLORS.textDefault }, { value: 'if', color: COLORS.keyword }, { value: ' ', color: COLORS.textDefault }, { value: 'not', color: COLORS.keyword }, { value: ' self.SAFE_PATTERN.match(sanitized):', color: COLORS.textDefault }] },
  { text: '            return None', tokens: [{ value: '            ', color: COLORS.textDefault }, { value: 'return', color: COLORS.keyword }, { value: ' ', color: COLORS.textDefault }, { value: 'None', color: COLORS.keyword }] },
  { text: '        user_name = sanitized.strip()', tokens: [{ value: '        user_name = sanitized.strip()', color: COLORS.textDefault }] },
  { text: '        return {"name": user_name, "valid": True}', tokens: [{ value: '        ', color: COLORS.textDefault }, { value: 'return', color: COLORS.keyword }, { value: ' {', color: COLORS.textDefault }, { value: '"name"', color: COLORS.string }, { value: ': user_name, ', color: COLORS.textDefault }, { value: '"valid"', color: COLORS.string }, { value: ': ', color: COLORS.textDefault }, { value: 'True', color: COLORS.keyword }, { value: '}', color: COLORS.textDefault }] },
  { text: '', tokens: [] },
];

// Test lines
export const EXISTING_TESTS = [
  'test_basic_parse',
  'test_empty_input',
  'test_unicode_name',
  'test_max_length',
];

export const NEW_TEST = 'test_null_injection';
