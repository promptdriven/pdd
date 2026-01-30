import { z } from "zod";

// Video specs
export const GROUNDING_DB_FPS = 30;
export const GROUNDING_DB_DURATION_SECONDS = 15;
export const GROUNDING_DB_DURATION_FRAMES =
  GROUNDING_DB_FPS * GROUNDING_DB_DURATION_SECONDS;
export const GROUNDING_DB_WIDTH = 1920;
export const GROUNDING_DB_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  SUCCESS_START: 0,
  SUCCESS_END: 60,
  DATA_HIGHLIGHT_START: 90,
  DATA_HIGHLIGHT_END: 120,
  FLOW_START: 150,
  FLOW_END: 250,
  DB_APPEAR_START: 200,
  DB_APPEAR_END: 260,
  DB_PULSE_START: 280,
  DB_PULSE_END: 340,
  FEEDBACK_START: 360,
  FEEDBACK_END: 400,
  QUOTE_START: 420,
  HOLD_START: 420,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  GROUNDING_GREEN: "#5AAA6E",
  SUCCESS_GREEN: "#4CAF50",
  CODE_GRAY: "#8a9caf",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Props schema
export const GroundingDatabaseProps = z.object({
  showFeedbackLoop: z.boolean().default(true),
});

export const defaultGroundingDatabaseProps: z.infer<typeof GroundingDatabaseProps> = {
  showFeedbackLoop: true,
};

export type GroundingDatabasePropsType = z.infer<typeof GroundingDatabaseProps>;
