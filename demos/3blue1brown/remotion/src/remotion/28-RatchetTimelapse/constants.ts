import { z } from "zod";

// Video specs
export const RATCHET_FPS = 30;
export const RATCHET_DURATION_SECONDS = 25;
export const RATCHET_DURATION_FRAMES =
  RATCHET_FPS * RATCHET_DURATION_SECONDS;
export const RATCHET_WIDTH = 1920;
export const RATCHET_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  INITIAL_WALLS_START: 0,
  INITIAL_WALLS_END: 60,
  TIMELAPSE_START: 90,
  TIMELAPSE_END: 540,
  WALL_ACCUMULATION_RATE: 30, // New wall every 30 frames during timelapse
  COUNTER_START: 120,
  INSIGHT_START: 600,
  HOLD_START: 720,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  WALLS_AMBER: "#D9944A",
  COUNTER_BLUE: "#4A90D9",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Test wall labels that accumulate over time
export const ACCUMULATING_TESTS = [
  "null → None",
  "empty → None",
  '"abc" → "abc"',
  '" abc " → "abc"',
  '"a1b2" → "a1b2"',
  '"a@b" → None',
  '"" → None',
  '" " → None',
  '"ABC" → "ABC"',
  '"123" → "123"',
  '"a_b" → None',
  '"a-b" → None',
  '"a.b" → None',
  '"very_long_id" → None',
  '"id123" → "id123"',
];

// Props schema
export const RatchetTimelapseProps = z.object({
  maxWalls: z.number().default(15),
});

export const defaultRatchetTimelapseProps: z.infer<typeof RatchetTimelapseProps> = {
  maxWalls: 15,
};

export type RatchetTimelapsePropsType = z.infer<typeof RatchetTimelapseProps>;
