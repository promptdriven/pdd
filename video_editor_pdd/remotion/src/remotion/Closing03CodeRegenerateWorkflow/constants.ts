// === Colors ===
export const BG_COLOR = '#0A1628';
export const PANEL_BG = '#1E293B';
export const TERMINAL_BG = '#0F172A';
export const TEXT_DEFAULT = '#E2E8F0';
export const TEXT_MUTED = '#94A3B8';
export const HEADER_COLOR = '#64748B';
export const KEYWORD_BLUE = '#4A90D9';
export const STRING_GREEN = '#5AAA6E';
export const BUG_RED = '#EF4444';
export const AMBER_HIGHLIGHT = '#D9944A';
export const PASS_GREEN = '#22C55E';
export const ANNOTATION_UNDERLINE = '#4A90D9';

// === Dimensions ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;

export const CODE_PANEL = { x: 60, y: 80, width: 860, height: 700 };
export const TEST_PANEL = { x: 940, y: 80, width: 920, height: 700 };
export const TERMINAL_STRIP = { x: 60, y: 820, width: 1800, height: 200 };

// === Frame timings ===
export const FRAME_LAYOUT_IN = 0;
export const FRAME_PDD_BUG_START = 30;
export const FRAME_PDD_FIX_START = 70;
export const FRAME_CODE_DISSOLVE_START = 100;
export const FRAME_CODE_STREAM_START = 130;
export const FRAME_TESTS_PASS = 160;
export const FRAME_ANNOTATION = 200;
export const FRAME_HOLD = 250;
export const TOTAL_FRAMES = 300;

// === Fonts ===
export const MONO_FONT = 'JetBrains Mono, Menlo, Monaco, Consolas, monospace';
export const SANS_FONT = 'Inter, system-ui, sans-serif';

// === Original code (with bug on line index 11) ===
export const ORIGINAL_CODE: Array<{text: string; type: 'default' | 'keyword' | 'string' | 'comment' | 'bug'}> = [
	{ text: 'import re', type: 'keyword' },
	{ text: 'from typing import Optional', type: 'keyword' },
	{ text: '', type: 'default' },
	{ text: 'class UserParser:', type: 'keyword' },
	{ text: '    """Parse and validate user input."""', type: 'string' },
	{ text: '', type: 'default' },
	{ text: '    def __init__(self, strict=True):', type: 'keyword' },
	{ text: '        self.strict = strict', type: 'default' },
	{ text: '        self._cache = {}', type: 'default' },
	{ text: '', type: 'default' },
	{ text: '    def parse_name(self, raw: str) -> str:', type: 'keyword' },
	{ text: '        name = raw.strip()', type: 'default' },
	{ text: '        # BUG: no null-byte sanitization', type: 'bug' },
	{ text: '        return name', type: 'bug' },
	{ text: '', type: 'default' },
	{ text: '    def validate(self, data: dict) -> bool:', type: 'keyword' },
	{ text: '        if not data.get("name"):', type: 'default' },
	{ text: '            return False', type: 'default' },
	{ text: '        return len(data["name"]) <= 255', type: 'default' },
];

// === Regenerated code (clean, no bug) ===
export const REGENERATED_CODE: Array<{text: string; type: 'default' | 'keyword' | 'string' | 'comment'}> = [
	{ text: 'import re', type: 'keyword' },
	{ text: 'from typing import Optional', type: 'keyword' },
	{ text: '', type: 'default' },
	{ text: 'class UserParser:', type: 'keyword' },
	{ text: '    """Parse and validate user input fields."""', type: 'string' },
	{ text: '', type: 'default' },
	{ text: '    def __init__(self, mode="strict"):', type: 'keyword' },
	{ text: '        self.mode = mode', type: 'default' },
	{ text: '        self._seen = set()', type: 'default' },
	{ text: '', type: 'default' },
	{ text: '    def parse_name(self, raw: str) -> str:', type: 'keyword' },
	{ text: '        cleaned = raw.strip()', type: 'default' },
	{ text: '        cleaned = cleaned.replace("\\x00", "")', type: 'string' },
	{ text: '        cleaned = re.sub(r"[\\x00-\\x1f]", "", cleaned)', type: 'string' },
	{ text: '        return cleaned', type: 'default' },
	{ text: '', type: 'default' },
	{ text: '    def validate(self, fields: dict) -> bool:', type: 'keyword' },
	{ text: '        name = fields.get("name", "")', type: 'default' },
	{ text: '        return bool(name) and len(name) <= 255', type: 'default' },
];

// === Test lines ===
export const EXISTING_TESTS = [
	'test_basic_parse',
	'test_empty_input',
	'test_unicode_name',
	'test_max_length',
];

export const NEW_TEST = 'test_null_injection';

// === Terminal commands ===
export const TERMINAL_COMMANDS = [
	{ command: 'pdd bug user_parser', output: 'Creating failing test...' },
	{ command: 'pdd fix user_parser', output: 'Regenerating...' },
];
