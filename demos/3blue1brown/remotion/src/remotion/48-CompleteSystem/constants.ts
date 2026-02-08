import { z } from "zod";

// Video specs
export const COMPLETE_SYSTEM_FPS = 30;
export const COMPLETE_SYSTEM_DURATION_SECONDS = 10;
export const COMPLETE_SYSTEM_DURATION_FRAMES =
  COMPLETE_SYSTEM_FPS * COMPLETE_SYSTEM_DURATION_SECONDS;
export const COMPLETE_SYSTEM_WIDTH = 1920;
export const COMPLETE_SYSTEM_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  // Camera pull-back (zoom out)
  ZOOM_START: 0,
  ZOOM_END: 60,

  // Prompt glows activate (staggered per module)
  PROMPT_GLOW_START: 60,
  PROMPT_GLOW_STAGGER: 10, // frames between each module

  // Test glows activate (staggered, after prompts)
  TEST_GLOW_START: 100,
  TEST_GLOW_STAGGER: 10,

  // Code dims
  CODE_DIM_START: 150,
  CODE_DIM_END: 200,

  // Hold
  HOLD_START: 240,
};

// Module definitions
export const MODULES = [
  { name: "auth", x: 280, y: 180 },
  { name: "parser", x: 680, y: 180 },
  { name: "api", x: 280, y: 520 },
  { name: "db", x: 680, y: 520 },
  { name: "utils", x: 1080, y: 350 },
];

// Connection lines between modules (index pairs)
export const CONNECTIONS = [
  [0, 1], // auth -> parser
  [0, 2], // auth -> api
  [1, 3], // parser -> db
  [2, 3], // api -> db
  [1, 4], // parser -> utils
  [2, 4], // api -> utils
];

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  PROMPT_BLUE: "#4A90D9",
  TEST_AMBER: "#D9944A",
  CODE_GRAY: "#A0A0A0",
  LABEL_WHITE: "#ffffff",
  LABEL_DIM: "rgba(255, 255, 255, 0.5)",
};

// Props schema
export const CompleteSystemProps = z.object({
  showConnections: z.boolean().default(true),
});

export const defaultCompleteSystemProps: z.infer<typeof CompleteSystemProps> = {
  showConnections: true,
};

export type CompleteSystemPropsType = z.infer<typeof CompleteSystemProps>;
