import { z } from "zod";

// Video specs
export const WALLS_ILLUMINATE_FPS = 30;
export const WALLS_ILLUMINATE_DURATION_SECONDS = 15;
export const WALLS_ILLUMINATE_DURATION_FRAMES =
  WALLS_ILLUMINATE_FPS * WALLS_ILLUMINATE_DURATION_SECONDS;
export const WALLS_ILLUMINATE_WIDTH = 1920;
export const WALLS_ILLUMINATE_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  MOLD_VISIBLE_START: 0,
  MOLD_VISIBLE_END: 30,
  WALLS_GLOW_START: 30,
  WALLS_GLOW_END: 90,
  LABELS_START: 90,
  LABELS_STAGGER: 30, // 30 frames between each label
  HOLD_START: 360,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  WALLS_AMBER: "#D9944A",
  WALLS_AMBER_DIM: "rgba(217, 148, 74, 0.3)",
  OUTLINE_GRAY: "#5a6a7a",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Test labels to display on walls
export const TEST_LABELS = [
  "null → None",
  "empty → None",
  '"abc" → "abc"',
  '" abc " → "abc"',
  '"a1b2" → "a1b2"',
  '"a@b" → None',
];

// Props schema
export const WallsIlluminateProps = z.object({
  showLabels: z.boolean().default(true),
});

export const defaultWallsIlluminateProps: z.infer<typeof WallsIlluminateProps> = {
  showLabels: true,
};

export type WallsIlluminatePropsType = z.infer<typeof WallsIlluminateProps>;
