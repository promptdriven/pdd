import { z } from "zod";

// Video specs
export const BOTH_GENERATE_FPS = 30;
export const BOTH_GENERATE_DURATION_SECONDS = 15;
export const BOTH_GENERATE_DURATION_FRAMES =
  BOTH_GENERATE_FPS * BOTH_GENERATE_DURATION_SECONDS;
export const BOTH_GENERATE_WIDTH = 1920;
export const BOTH_GENERATE_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// 0-3s: Split screen setup (frames 0-90)
// 3-7s: Generation animation (frames 90-210)
// 7-10s: Both succeed (frames 210-300)
// 10-15s: Final message (frames 300-450)
export const BEATS = {
  // Setup phase
  SETUP_START: 0,
  SETUP_END: 60,
  VERSIONS_VISIBLE: 90,

  // Generation phase
  GENERATION_START: 90,
  GENERATION_END: 210,

  // Success phase
  SUCCESS_START: 210,
  SUCCESS_END: 270,

  // Final message phase
  DIM_START: 300,
  DIM_END: 360,
  MESSAGE_START: 300,
  MESSAGE_END: 390,
  HOLD_START: 390,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  NOZZLE_BLUE: "#4A90D9",
  WALLS_AMBER: "#D9944A",
  SUCCESS_GREEN: "#5AAA6E",
  CODE_GRAY: "#8a9caf",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
  DIVIDER: "rgba(255, 255, 255, 0.2)",
  CODE_BG: "#1E1E2E",
  LINE_PLACEHOLDER: "rgba(255, 255, 255, 0.2)",
  CODE_LINE: "rgba(160, 160, 160, 0.3)",
};

// Props schema
export const BothGenerateFinalProps = z.object({
  showFinalMessage: z.boolean().default(true),
});

export const defaultBothGenerateFinalProps: z.infer<typeof BothGenerateFinalProps> = {
  showFinalMessage: true,
};

export type BothGenerateFinalPropsType = z.infer<typeof BothGenerateFinalProps>;
