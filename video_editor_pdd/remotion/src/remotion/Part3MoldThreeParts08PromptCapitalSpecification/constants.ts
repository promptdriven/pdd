// Component-level constants for Part3MoldThreeParts08PromptCapitalSpecification

export const COLORS = {
  background: '#0A0F1A',
  gridLine: '#1E293B',
  nozzleBlue: '#4A90D9',
  codePanel: '#1E293B',
  codeBorder: '#334155',
  checkmarkGreen: '#5AAA6E',
  labelMuted: '#64748B',
  textLight: '#E2E8F0',
  codeText: '#94A3B8',
  behaviorGreen: '#5AAA6E',
} as const;

export const CANVAS = {
  width: 1920,
  height: 1080,
} as const;

export const GRID_SPACING = 40;
export const GRID_OPACITY = 0.03;

// Beat frame ranges
export const BEAT1_START = 0;
export const BEAT1_END = 150;
export const BEAT2_START = 150;
export const BEAT2_END = 360;
export const BEAT3_START = 360;
export const BEAT3_END = 600;
export const TOTAL_FRAMES = 600;

// Prompt content
export const PROMPT_TEXT =
  'Parse user IDs from untrusted input. Return None on failure, never throw. Handle unicode.';

export const PROMPT_FILE = 'user_parser.prompt';

// Code for Generation A (OOP style)
export const CODE_A = `import re
from typing import Optional

class UserParser:
    """Parse user IDs from untrusted input."""

    PATTERN = re.compile(
        r'^[a-zA-Z][\\w.-]{2,31}$'
    )

    def __init__(self, strict: bool = True):
        self._strict = strict
        self._cache: dict[str, bool] = {}

    def parse(
        self, raw: str
    ) -> Optional[str]:
        if not isinstance(raw, str):
            return None
        cleaned = raw.strip()
        if not cleaned:
            return None
        try:
            normalized = cleaned.encode(
                'utf-8'
            ).decode('utf-8')
        except (UnicodeError, ValueError):
            return None
        if not self.PATTERN.match(
            normalized
        ):
            return None
        return normalized`;

// Code for Generation B (functional style)
export const CODE_B = `import re
from typing import Optional

_UID_RE = re.compile(
    r'^[a-zA-Z][\\w.-]{2,31}$'
)

def parse_user_id(
    raw_input: str,
) -> Optional[str]:
    if not isinstance(raw_input, str):
        return None

    value = raw_input.strip()
    if not value:
        return None

    try:
        safe = value.encode(
            'utf-8'
        ).decode('utf-8')
    except (UnicodeError, ValueError):
        return None

    if not _UID_RE.match(safe):
        return None

    return safe


def batch_parse(
    items: list[str],
) -> list[Optional[str]]:
    return [
        parse_user_id(i) for i in items
    ]`;

// Short prompt for compression ratio view
export const SHORT_PROMPT_LINES = [
  '# user_parser.prompt',
  '',
  'Parse user IDs from untrusted input.',
  'Return None on failure — never throw.',
  'Handle unicode edge cases.',
  '',
  'Constraints:',
  '  - Max 32 chars, alphanumeric + . -',
  '  - Must start with a letter',
  '  - Strip whitespace before parsing',
  '  - Cache valid lookups (optional)',
  '',
  'Output: Optional[str]',
];

// Module prompts for context window comparison
export const MODULE_PROMPTS = [
  'auth_handler.prompt',
  'user_parser.prompt',
  'rate_limiter.prompt',
  'session_manager.prompt',
  'input_validator.prompt',
  'cache_layer.prompt',
  'error_handler.prompt',
  'config_loader.prompt',
  'db_connector.prompt',
  'api_router.prompt',
];
