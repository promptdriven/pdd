import { z } from "zod";

// Video specs
export const ADD_TEST_WALL_FPS = 30;
export const ADD_TEST_WALL_DURATION_SECONDS = 15;
export const ADD_TEST_WALL_DURATION_FRAMES =
  ADD_TEST_WALL_FPS * ADD_TEST_WALL_DURATION_SECONDS;
export const ADD_TEST_WALL_WIDTH = 1920;
export const ADD_TEST_WALL_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  WALLS_VISIBLE_START: 0,
  WALLS_VISIBLE_END: 30,
  NEW_WALL_START: 60,
  NEW_WALL_END: 120,
  CLICK_SOUND: 90,
  LABEL_START: 150,
  GLOW_START: 180,
  GLOW_END: 240,
  HOLD_START: 360,
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
