import { z } from "zod";

// Video specs
export const SHORT_PROMPT_FPS = 30;
export const SHORT_PROMPT_DURATION_SECONDS = 15;
export const SHORT_PROMPT_DURATION_FRAMES =
  SHORT_PROMPT_FPS * SHORT_PROMPT_DURATION_SECONDS;
export const SHORT_PROMPT_WIDTH = 1920;
export const SHORT_PROMPT_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Based on spec: 15 seconds total
// Frame 0-90 (0-3s): Prompt appears
// Frame 90-210 (3-7s): Test walls materialize
// Frame 210-330 (7-11s): Terminal appears
// Frame 330-450 (11-15s): Hold
export const BEATS = {
  PROMPT_START: 0,
  PROMPT_END: 90,
  WALLS_START: 90,
  WALLS_END: 210,
  TERMINAL_START: 210,
  TERMINAL_END: 270,
  HOLD_START: 330,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  NOZZLE_BLUE: "#4A90D9",
  WALLS_AMBER: "#D9944A",
  SUCCESS_GREEN: "#5AAA6E",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "rgba(255, 255, 255, 0.7)",
  TERMINAL_BG: "rgba(30, 30, 46, 0.95)",
  FILE_CONTENT_BG: "#1E1E2E",
};

// Short prompt content
export const SHORT_PROMPT_CONTENT = `# User ID Parser

Parse and validate user IDs from input.
Return None for any invalid input.
Handle all edge cases gracefully.
Never throw exceptions.

See tests for exact behavior.`;

// Wall configuration
export const WALL_COUNT = 30;
export const CENTER_X = 960;
export const CENTER_Y = 540;
export const INNER_RADIUS = 300;

// Props schema
export const ShortPromptTestsProps = z.object({
  showTerminal: z.boolean().default(true),
});

export const defaultShortPromptTestsProps: z.infer<typeof ShortPromptTestsProps> = {
  showTerminal: true,
};

export type ShortPromptTestsPropsType = z.infer<typeof ShortPromptTestsProps>;
