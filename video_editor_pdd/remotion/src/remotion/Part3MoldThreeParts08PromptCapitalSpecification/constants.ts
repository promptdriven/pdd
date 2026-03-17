// ── Colors ──
export const BG = '#0A0F1A';
export const GRID_COLOR = '#1E293B';
export const GRID_OPACITY = 0.03;

export const NOZZLE_BLUE = '#4A90D9';
export const CHECK_GREEN = '#5AAA6E';
export const MUTED_GRAY = '#64748B';
export const CODE_DIM = '#94A3B8';
export const PANEL_BG = '#1E293B';
export const PANEL_BORDER = '#334155';
export const TEXT_LIGHT = '#E2E8F0';

// ── Dimensions ──
export const WIDTH = 1920;
export const HEIGHT = 1080;
export const GRID_SPACING = 40;

// ── Beat boundaries (frames) ──
export const BEAT1_START = 0;
export const BEAT1_END = 150;
export const BEAT2_START = 150;
export const BEAT2_END = 360;
export const BEAT3_START = 360;
export const BEAT3_END = 600;
export const TOTAL_FRAMES = 600;

// ── Prompt content ──
export const PROMPT_TEXT =
  'Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode.';

export const PROMPT_LINES = [
  '# user_parser.prompt',
  '',
  'Parse user IDs from untrusted input.',
  'Return None on failure — never throw.',
  'Handle unicode identifiers.',
  'Accept str | bytes | int.',
  'Strip whitespace and control chars.',
  'Validate against [a-zA-Z0-9_-].',
  'Max length: 128 characters.',
  'Log malformed inputs at DEBUG level.',
  'Thread-safe, no global state.',
  'Return UserID | None.',
];

// ── Code samples ──
export const CODE_V1 = `class UserParser:
    """Parse user IDs from untrusted input."""

    MAX_LEN = 128
    PATTERN = re.compile(r'^[a-zA-Z0-9_-]+$')

    def __init__(self, logger=None):
        self._log = logger or logging.getLogger()

    def parse(self, raw: str | bytes | int) -> UserID | None:
        try:
            text = self._normalize(raw)
            text = text.strip()
            text = self._strip_control(text)
            if len(text) > self.MAX_LEN:
                self._log.debug("too long: %d", len(text))
                return None
            if not self.PATTERN.match(text):
                self._log.debug("bad chars: %r", text)
                return None
            return UserID(text)
        except Exception:
            self._log.debug("parse failed", exc_info=True)
            return None

    def _normalize(self, raw):
        if isinstance(raw, bytes):
            return raw.decode('utf-8', errors='replace')
        if isinstance(raw, int):
            return str(raw)
        return str(raw)

    def _strip_control(self, s):
        return ''.join(c for c in s if not unicodedata.category(c).startswith('C'))`;

export const CODE_V2 = `def parse_user_id(raw_input: str | bytes | int) -> UserID | None:
    """Parse user IDs safely. Never throws."""

    _MAX = 128
    _VALID = re.compile(r'^[a-zA-Z0-9_-]+$')

    def to_str(val):
        match val:
            case bytes():
                return val.decode('utf-8', errors='replace')
            case int():
                return str(val)
            case _:
                return str(val)

    try:
        cleaned = to_str(raw_input).strip()
        cleaned = remove_control_chars(cleaned)

        if len(cleaned) > _MAX:
            log.debug(f"Rejected: length {len(cleaned)}")
            return None
        if not _VALID.fullmatch(cleaned):
            log.debug(f"Rejected: invalid chars")
            return None

        return UserID(value=cleaned)
    except Exception:
        log.debug("Failed to parse", exc_info=True)
        return None


def remove_control_chars(text: str) -> str:
    return ''.join(
        ch for ch in text
        if unicodedata.category(ch)[0] != 'C'
    )`;

// ── Dense code for scrolling panel ──
export const DENSE_CODE_LINES: string[] = [];
const fragments = [
  'def validate(self, data):',
  '    if not isinstance(data, dict):',
  '        raise TypeError("expected dict")',
  '    for key, val in data.items():',
  '        self._check_field(key, val)',
  '    return True',
  '',
  'class InputHandler:',
  '    def __init__(self, config):',
  '        self.config = config',
  '        self._cache = {}',
  '        self._lock = threading.Lock()',
  '',
  '    def process(self, raw):',
  '        normalized = self._normalize(raw)',
  '        if normalized in self._cache:',
  '            return self._cache[normalized]',
  '        result = self._compute(normalized)',
  '        with self._lock:',
  '            self._cache[normalized] = result',
  '        return result',
  '',
  '    def _normalize(self, val):',
  '        return str(val).strip().lower()',
  '',
  '    def _compute(self, val):',
  '        tokens = self._tokenize(val)',
  '        return self._assemble(tokens)',
];
// Repeat to get 200+ lines
for (let i = 0; i < 8; i++) {
  DENSE_CODE_LINES.push(...fragments);
}
