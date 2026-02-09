import { z } from "zod";

// Video specs
export const GROUNDING_DB_FPS = 30;
export const GROUNDING_DB_DURATION_SECONDS = 15;
export const GROUNDING_DB_DURATION_FRAMES =
  GROUNDING_DB_FPS * GROUNDING_DB_DURATION_SECONDS;
export const GROUNDING_DB_WIDTH = 1920;
export const GROUNDING_DB_HEIGHT = 1080;

// Beat timings (in frames at 30fps) - aligned with spec
export const BEATS = {
  SUCCESS_START: 0,
  SUCCESS_END: 90,           // Extended from 60 to 90 (0-3s)
  DATA_HIGHLIGHT_START: 90,
  DATA_HIGHLIGHT_END: 180,   // Extended from 120 to 180 (3-6s)
  FLOW_START: 180,           // Shifted from 150 to 180
  FLOW_END: 300,             // Extended from 250 to 300 (6-10s)
  DB_APPEAR_START: 240,
  DB_APPEAR_END: 300,        // Extended from 260 to 300
  DB_PULSE_START: 300,       // Shifted from 280 to 300
  DB_PULSE_END: 390,         // Extended from 340 to 390 (10-13s)
  FEEDBACK_START: 390,       // Shifted from 360 to 390
  FEEDBACK_END: 450,         // Extended from 400 to 450 (13-15s)
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
