import { z } from "zod";

// Video specs
export const FOCUS_WALL_FPS = 30;
export const FOCUS_WALL_DURATION_SECONDS = 15;
export const FOCUS_WALL_DURATION_FRAMES =
  FOCUS_WALL_FPS * FOCUS_WALL_DURATION_SECONDS;
export const FOCUS_WALL_WIDTH = 1920;
export const FOCUS_WALL_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  WALL_VISIBLE_START: 0,
  WALL_VISIBLE_END: 30,
  ZOOM_START: 30,
  ZOOM_END: 120,
  // Liquid approach (frames 120-180)
  LIQUID_APPROACH_START: 120,
  LIQUID_APPROACH_END: 180,
  // Impact moment (frame 180)
  IMPACT_FRAME: 180,
  // Wall glow / highlight
  HIGHLIGHT_START: 180,
  HIGHLIGHT_END: 210,
  // Splash dissipation
  SPLASH_END: 210,
  EXPLANATION_START: 240,
  HOLD_START: 360,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  WALLS_AMBER: "#D9944A",
  HIGHLIGHT_YELLOW: "#FFD700",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
  LIQUID_BLUE: "#8A9CAF",
  IMPACT_AMBER: "#FFAA55",
};

// The test case to focus on
export const FOCUS_TEST = {
  input: "null",
  output: "None",
  description: "Empty/null input returns None",
};

// Props schema
export const FocusSingleWallProps = z.object({
  testInput: z.string().default("null"),
  testOutput: z.string().default("None"),
});

export const defaultFocusSingleWallProps: z.infer<typeof FocusSingleWallProps> = {
  testInput: "null",
  testOutput: "None",
};

export type FocusSingleWallPropsType = z.infer<typeof FocusSingleWallProps>;
