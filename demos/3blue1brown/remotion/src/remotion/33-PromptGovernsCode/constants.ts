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

// The compact prompt
export const PROMPT_LINES = [
  "Parse user ID from untrusted input.",
  "Strip whitespace, validate alphanumeric.",
  "Return None for invalid input.",
  "Handle empty strings and null values.",
];

// Generated code (abbreviated representation)
export const CODE_PREVIEW = `def parse_user_id(input_str: str) -> Optional[str]:
    \"\"\"Parse and validate user ID from untrusted input.

    Args:
        input_str: Raw input string that may contain
                   whitespace or invalid characters.

    Returns:
        Cleaned alphanumeric user ID, or None if invalid.

    Examples:
        >>> parse_user_id("  abc123  ")
        'abc123'
        >>> parse_user_id("invalid@id")
        None
    \"\"\"
    if input_str is None:
        return None

    if not isinstance(input_str, str):
        return None

    cleaned = input_str.strip()

    if not cleaned:
        return None

    if not cleaned.isalnum():
        return None

    return cleaned`;

// Props schema
export const PromptGovernsCodeProps = z.object({
  promptLineCount: z.number().default(12),
  codeLineCount: z.number().default(200),
});

export const defaultPromptGovernsCodeProps: z.infer<typeof PromptGovernsCodeProps> = {
  promptLineCount: 12,
  codeLineCount: 200,
};

export type PromptGovernsCodePropsType = z.infer<typeof PromptGovernsCodeProps>;
