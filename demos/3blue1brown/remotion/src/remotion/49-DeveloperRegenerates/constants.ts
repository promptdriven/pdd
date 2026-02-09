import { z } from "zod";

// Video specs
export const DEV_REGENERATES_FPS = 30;
export const DEV_REGENERATES_DURATION_SECONDS = 15;
export const DEV_REGENERATES_DURATION_FRAMES =
  DEV_REGENERATES_FPS * DEV_REGENERATES_DURATION_SECONDS;
export const DEV_REGENERATES_WIDTH = 1920;
export const DEV_REGENERATES_HEIGHT = 1080;

// Beat timings (in frames at 30fps) - matched to spec
export const BEATS = {
  // Terminal fades in
  TERMINAL_FADE_START: 0,
  TERMINAL_FADE_END: 30,

  // Bug command types out (spec: 90-130)
  BUG_CMD_START: 90,
  BUG_CMD_END: 130,
  BUG_OUTPUT_START: 135,
  BUG_OUTPUT_END: 150,

  // Fix command types out (spec: 150-190)
  FIX_CMD_START: 150,
  FIX_CMD_END: 190,
  FIX_REGEN_START: 195,
  FIX_REGEN_END: 210,
  FIX_OUTPUT_START: 215,
  FIX_OUTPUT_END: 235,

  // Test command types out (spec: 240-280)
  TEST_CMD_START: 240,
  TEST_CMD_END: 280,
  TEST_OUTPUT_START: 290,
  TEST_OUTPUT_END: 310,

  // Checkmark pop (spec: 310-340-360)
  CHECK_START: 310,
  CHECK_POP: 340,
  CHECK_SETTLE: 360,

  // Hold
  HOLD_START: 360,
};

// Terminal commands
export const COMMANDS = [
  { text: "pdd bug parser", color: "#D9944A" },
  { text: "pdd fix parser", color: "#4A90D9" },
  { text: "pdd test parser", color: "#5AAA6E" },
];

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  TERMINAL_BG: "rgba(30, 30, 46, 0.92)",
  TERMINAL_BORDER: "rgba(255, 255, 255, 0.15)",
  BUG_AMBER: "#D9944A",
  FIX_BLUE: "#4A90D9",
  TEST_GREEN: "#5AAA6E",
  ERROR_RED: "rgba(255, 100, 100, 0.8)",
  TEXT_DIM: "rgba(255, 255, 255, 0.5)",
  TEXT_NORMAL: "rgba(255, 255, 255, 0.7)",
  LABEL_WHITE: "#ffffff",
};

// Props schema
export const DeveloperRegeneratesProps = z.object({
  showTerminal: z.boolean().default(true),
});

export const defaultDeveloperRegeneratesProps: z.infer<typeof DeveloperRegeneratesProps> = {
  showTerminal: true,
};

export type DeveloperRegeneratesPropsType = z.infer<typeof DeveloperRegeneratesProps>;
