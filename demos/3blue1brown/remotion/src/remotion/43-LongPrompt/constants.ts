import { z } from "zod";

// Video specs
export const LONG_PROMPT_FPS = 30;
export const LONG_PROMPT_DURATION_SECONDS = 15;
export const LONG_PROMPT_DURATION_FRAMES =
  LONG_PROMPT_FPS * LONG_PROMPT_DURATION_SECONDS;
export const LONG_PROMPT_WIDTH = 1920;
export const LONG_PROMPT_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// ~15 seconds = 450 frames
export const BEATS = {
  // Frame 0-90 (0-3s): Prompt file appears
  CONTAINER_FADE_START: 0,
  CONTAINER_FADE_END: 90,
  // Frame 90-270 (3-9s): Content reveals / scroll
  SCROLL_START: 90,
  SCROLL_END: 270,
  // Frame 270-360 (9-12s): Test walls appear
  WALLS_FADE_START: 270,
  WALLS_FADE_END: 330,
  // Frame 360-450 (12-15s): Hold
  HOLD_START: 360,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  HEADER_BLUE: "#4A90D9",
  WALLS_AMBER: "#D9944A",
  CONTENT_BG: "#1E1E2E",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
  TEXT_GRAY: "rgba(255, 255, 255, 0.8)",
  BULLET_ORANGE: "#D9944A",
};

// Long prompt content (50 lines)
export const PROMPT_CONTENT = `# User ID Parser - Version 1

## Purpose
Parse and validate user IDs from untrusted input sources.

## Input Handling
- Accept string input from any source
- Handle null/undefined gracefully
- Handle empty strings
- Handle whitespace-only strings
- Trim leading and trailing whitespace

## Validation Rules
- Must be alphanumeric plus underscore and hyphen
- Minimum length: 1 character
- Maximum length: 64 characters
- Case-insensitive comparison
- No leading or trailing hyphens
- No consecutive underscores

## Unicode Support
- Accept Unicode letters in addition to ASCII
- Normalize to NFC form before processing
- Handle combining characters correctly

## Error Handling
- Never throw exceptions
- Return None for invalid input
- Log validation failures for debugging
- Provide error context in logs

## Edge Cases
- Single character IDs are valid
- Numeric-only IDs are valid
- IDs starting with numbers are valid
- Empty after trimming -> None
- Only special chars -> None

## Performance
- O(n) complexity maximum
- No regex compilation per call
- Cache validation patterns

## Return Value
- Valid: cleaned string
- Invalid: None (never raise)

## Logging
- Debug: all inputs
- Warning: validation failures
- Error: never (no exceptions)`;

// Props schema
export const LongPromptProps = z.object({
  showTestWalls: z.boolean().default(true),
});

export const defaultLongPromptProps: z.infer<typeof LongPromptProps> = {
  showTestWalls: true,
};

export type LongPromptPropsType = z.infer<typeof LongPromptProps>;
