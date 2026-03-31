// === Colors ===
export const BG_DEEP_NAVY = '#0A0F1A';
export const EDITOR_BG = '#1E1E2E';
export const TERMINAL_BG = '#11111B';
export const TEXT_PRIMARY = '#CDD6F4';
export const TEXT_MUTED = '#94A3B8';
export const COLOR_RED = '#F38BA8';
export const COLOR_GREEN = '#A6E3A1';
export const COLOR_YELLOW = '#F9E2AF';
export const COLOR_BLUE = '#89B4FA';
export const COLOR_MAUVE = '#CBA6F7';
export const COLOR_PEACH = '#FAB387';
export const COLOR_TEAL = '#94E2D5';
export const COLOR_SURFACE0 = '#313244';
export const COLOR_OVERLAY0 = '#6C7086';

// === Layout ===
export const CANVAS_WIDTH = 1920;
export const CANVAS_HEIGHT = 1080;
export const LEFT_PANEL_WIDTH = 1040;
export const RIGHT_PANEL_WIDTH = 840;
export const PANEL_GAP = 40;
export const PANEL_PADDING_X = 20;
export const PANEL_PADDING_Y = 16;
export const PANEL_BORDER_RADIUS = 8;
export const TITLE_BAR_HEIGHT = 36;

// === Typography ===
export const CODE_FONT = 'JetBrains Mono, Fira Code, Consolas, monospace';
export const CODE_FONT_SIZE = 12;
export const TERMINAL_FONT_SIZE = 13;
export const SUMMARY_FONT_SIZE = 14;
export const ERROR_FONT_SIZE = 11;
export const CODE_LINE_HEIGHT = 1.65;
export const TERMINAL_LINE_HEIGHT = 1.7;

// === Timing (frames) ===
export const TOTAL_DURATION = 390;
export const FPS = 30;

// Phase boundaries
export const PHASE_LAYOUT_IN_START = 0;
export const PHASE_LAYOUT_IN_END = 30;
export const PHASE_FIRST_RUN_START = 30;
export const PHASE_FIRST_RUN_END = 60;
export const PHASE_FAILURE_START = 60;
export const PHASE_FAILURE_END = 100;
export const PHASE_HIGHLIGHT_START = 100;
export const PHASE_HIGHLIGHT_END = 130;
export const PHASE_FIX_CMD_START = 130;
export const PHASE_FIX_CMD_END = 160;
export const PHASE_REGEN_START = 160;
export const PHASE_REGEN_END = 210;
export const PHASE_SECOND_RUN_START = 210;
export const PHASE_SECOND_RUN_END = 250;
export const PHASE_RESULTS_START = 250;
export const PHASE_RESULTS_END = 340;
export const PHASE_SUMMARY_START = 340;
export const PHASE_SUMMARY_END = 370;
export const PHASE_HOLD_START = 370;
export const PHASE_HOLD_END = 390;

// === Code Content ===
export const EMAIL_VALIDATOR_V1 = `import re
from dataclasses import dataclass

@dataclass
class ValidationResult:
    valid: bool
    error: str | None = None

def validate_email(email: str) -> ValidationResult:
    """Validate an email address."""
    if not email or not email.strip():
        return ValidationResult(False, "Empty")

    pattern = r'^[a-zA-Z0-9._%+-]+@[a-zA-Z0-9.-]+\\.[a-zA-Z]{2,}$'
    if not re.match(pattern, email):
        return ValidationResult(False, "Invalid")

    local, domain = email.rsplit('@', 1)
    if len(local) > 64:
        return ValidationResult(False, "Local too long")

    if '..' in domain:
        return ValidationResult(False, "Invalid domain")

    return ValidationResult(True)`;

export const EMAIL_VALIDATOR_V2 = `import re
import idna
from dataclasses import dataclass

@dataclass
class ValidationResult:
    valid: bool
    error: str | None = None

def validate_email(email: str) -> ValidationResult:
    """Validate an email address with unicode support."""
    if not email or not email.strip():
        return ValidationResult(False, "Empty")

    local, _, domain = email.rpartition('@')
    if not local or not domain:
        return ValidationResult(False, "Invalid format")

    try:
        domain = idna.encode(domain).decode('ascii')
    except idna.IDNAError:
        return ValidationResult(False, "Invalid domain")

    pattern = r'^[a-zA-Z0-9._%+-]+$'
    if not re.match(pattern, local):
        return ValidationResult(False, "Invalid local")

    if len(local) > 64:
        return ValidationResult(False, "Local too long")

    return ValidationResult(True)`;

// === Test Data ===
export const TEST_RESULTS = [
  'test_basic_format',
  'test_invalid_domain',
  'test_empty_string',
  'test_special_chars',
  'test_unicode_domain',
] as const;

export const FAILING_TEST = 'test_unicode_domain';

export const ERROR_TRACE_LINES = [
  `    def test_unicode_domain():`,
  `        result = validate_email('user@münchen.de')`,
  `>       assert result.valid is True`,
  `E       AssertionError: assert False is True`,
  `E        +  where False = ValidationResult(valid=False, error='Invalid').valid`,
];

export const PDD_COMMAND = 'pdd fix email_validator';
export const PYTEST_COMMAND = 'pytest test_email_validator.py';
