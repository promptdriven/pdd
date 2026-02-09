import { z } from "zod";

// Video specs
export const PROMPT_GOVERNS_FPS = 30;
export const PROMPT_GOVERNS_DURATION_SECONDS = 20;
export const PROMPT_GOVERNS_DURATION_FRAMES =
  PROMPT_GOVERNS_FPS * PROMPT_GOVERNS_DURATION_SECONDS;
export const PROMPT_GOVERNS_WIDTH = 1920;
export const PROMPT_GOVERNS_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  PROMPT_START: 0,
  PROMPT_END: 60,
  ARROW_START: 90,
  ARROW_END: 150,
  CODE_EXPAND_START: 150,
  CODE_EXPAND_END: 360,
  RATIO_START: 400,
  INSIGHT_START: 500,
  HOLD_START: 560,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  NOZZLE_BLUE: "#4A90D9",
  CODE_GRAY: "#8a9caf",
  RATIO_GOLD: "#FFD700",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// The compact prompt (15 lines)
export const PROMPT_LINES = [
  "Parse user IDs from",
  "untrusted input.",
  "",
  "Return None on failure,",
  "never throw.",
  "",
  "Handle unicode.",
  "",
  "Strip whitespace.",
  "Validate alphanumeric.",
  "",
  "Log validation failures.",
  "",
  "Return cleaned string",
  "or None.",
];

// Generated code (200+ lines representation)
export const CODE_PREVIEW = `import re
import logging
from typing import Optional, Union
from unicodedata import normalize

logger = logging.getLogger(__name__)

class ValidationError(Exception):
    \"\"\"Raised when validation fails.\"\"\"
    pass

def parse_user_id(input_str: str) -> Optional[str]:
    \"\"\"Parse and validate user ID from untrusted input.

    This function handles a variety of edge cases including:
    - Null/empty input
    - Unicode normalization
    - Whitespace handling
    - Special character filtering
    - Type validation

    Args:
        input_str: Raw input string that may contain
                   whitespace or invalid characters.

    Returns:
        Cleaned alphanumeric user ID, or None if invalid.

    Raises:
        Never raises - returns None on any failure.

    Examples:
        >>> parse_user_id("  abc123  ")
        'abc123'
        >>> parse_user_id("invalid@id")
        None
        >>> parse_user_id("café123")
        'cafe123'
    \"\"\"
    # Type validation
    if input_str is None:
        logger.debug("Input is None")
        return None

    if not isinstance(input_str, str):
        logger.debug(f"Input is not string: {type(input_str)}")
        return None

    # Normalize unicode (NFC form)
    try:
        normalized = normalize('NFC', input_str)
    except Exception as e:
        logger.error(f"Unicode normalization failed: {e}")
        return None

    # Strip whitespace
    cleaned = normalized.strip()

    # Check for empty string
    if not cleaned:
        logger.debug("Input is empty after stripping")
        return None

    # Remove any non-alphanumeric characters
    alphanumeric_only = re.sub(r'[^a-zA-Z0-9]', '', cleaned)

    if not alphanumeric_only:
        logger.debug("No alphanumeric characters found")
        return None

    # Length validation
    if len(alphanumeric_only) < 3:
        logger.debug(f"ID too short: {len(alphanumeric_only)}")
        return None

    if len(alphanumeric_only) > 64:
        logger.debug(f"ID too long: {len(alphanumeric_only)}")
        return None

    # Pattern validation (must start with letter)
    if not alphanumeric_only[0].isalpha():
        logger.debug("ID must start with letter")
        return None

    # Success
    logger.info(f"Successfully parsed user ID: {alphanumeric_only}")
    return alphanumeric_only


def batch_parse_user_ids(inputs: list[str]) -> dict[str, Optional[str]]:
    \"\"\"Parse multiple user IDs in batch.

    Args:
        inputs: List of raw input strings

    Returns:
        Dictionary mapping original input to parsed ID (or None)
    \"\"\"
    results = {}
    for input_str in inputs:
        results[input_str] = parse_user_id(input_str)
    return results


def validate_user_id_format(user_id: str) -> bool:
    \"\"\"Validate that a user ID matches expected format.

    Args:
        user_id: User ID string to validate

    Returns:
        True if valid format, False otherwise
    \"\"\"
    if not user_id:
        return False

    if not isinstance(user_id, str):
        return False

    if not user_id.isalnum():
        return False

    if len(user_id) < 3 or len(user_id) > 64:
        return False

    if not user_id[0].isalpha():
        return False

    return True


# Additional utility functions...
def sanitize_for_display(user_id: str) -> str:
    \"\"\"Sanitize user ID for safe display.\"\"\"
    if not user_id:
        return "[empty]"
    # Truncate and add ellipsis if too long
    if len(user_id) > 20:
        return user_id[:20] + "..."
    return user_id


def compare_user_ids(id1: str, id2: str) -> bool:
    \"\"\"Case-insensitive comparison of user IDs.\"\"\"
    if not id1 or not id2:
        return False
    return id1.lower() == id2.lower()


# ... more helper functions continue for 200+ lines`;

// Props schema
export const PromptGovernsCodeProps = z.object({
  promptLineCount: z.number().default(15),
  codeLineCount: z.number().default(200),
});

export const defaultPromptGovernsCodeProps: z.infer<typeof PromptGovernsCodeProps> = {
  promptLineCount: 15,
  codeLineCount: 200,
};

export type PromptGovernsCodePropsType = z.infer<typeof PromptGovernsCodeProps>;
