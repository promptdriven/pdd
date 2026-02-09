import { z } from "zod";

// Video specs
export const ADD_TEST_WALL_FPS = 30;
export const ADD_TEST_WALL_DURATION_SECONDS = 15;
export const ADD_TEST_WALL_DURATION_FRAMES =
  ADD_TEST_WALL_FPS * ADD_TEST_WALL_DURATION_SECONDS;
export const ADD_TEST_WALL_WIDTH = 1920;
export const ADD_TEST_WALL_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Following spec: Frame 0-90 (return to mold), 90-180 (particles), 180-270 (solidify), 270-360 (click/lock), 360-600 (hold)
export const BEATS = {
  WALLS_VISIBLE_START: 0,
  WALLS_VISIBLE_END: 30,
  PARTICLES_START: 90,
  PARTICLES_END: 180,
  WALL_SOLIDIFY_START: 180,
  WALL_SOLIDIFY_END: 270,
  RATCHET_ENGAGE: 270,
  RATCHET_VISUAL_END: 300,
  LABEL_START: 240,
  TERMINAL_START: 60,
  TERMINAL_COMMAND_START: 90,
  TERMINAL_COMPLETE: 300,
  HOLD_START: 360,
  HOLD_END: 600,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  WALLS_AMBER: "#D9944A",
  NEW_WALL_GLOW: "#FFD700",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Existing test labels
export const EXISTING_TESTS = [
  "null → None",
  "empty → None",
  '"abc" → "abc"',
];

// New test being added
export const NEW_TEST = '" abc " → "abc"';

// Props schema
export const AddTestWallProps = z.object({
  showNewTest: z.boolean().default(true),
});

export const defaultAddTestWallProps: z.infer<typeof AddTestWallProps> = {
  showNewTest: true,
};

export type AddTestWallPropsType = z.infer<typeof AddTestWallProps>;
