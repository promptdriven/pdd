import { z } from "zod";

// Video specs
export const THREE_COMPONENTS_FPS = 30;
export const THREE_COMPONENTS_DURATION_SECONDS = 25;
export const THREE_COMPONENTS_DURATION_FRAMES =
  THREE_COMPONENTS_FPS * THREE_COMPONENTS_DURATION_SECONDS;
export const THREE_COMPONENTS_WIDTH = 1920;
export const THREE_COMPONENTS_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  // Vertices appear (staggered)
  VERTEX_PROMPT_START: 0,
  VERTEX_TESTS_START: 10,
  VERTEX_GROUNDING_START: 20,
  VERTEX_APPEAR_END: 50,

  // Edges connect
  EDGES_START: 60,
  EDGES_END: 120,

  // Glows intensify + sub-labels
  GLOW_INTENSIFY_START: 120,
  GLOW_INTENSIFY_END: 160,
  SUBLABEL_START: 130,
  SUBLABEL_END: 170,

  // Center code appears
  CODE_START: 180,
  CODE_END: 220,
  ARROWS_START: 200,
  ARROWS_END: 240,

  // Hold
  HOLD_START: 240,

  // Integration formula (appears after hold begins)
  FORMULA_START: 600,
  FORMULA_END: 660,
};

// Triangle geometry
export const TRIANGLE = {
  CENTER_X: 960,
  CENTER_Y: 440,
  // Vertex positions
  PROMPT: { x: 960, y: 180 },
  TESTS: { x: 560, y: 700 },
  GROUNDING: { x: 1360, y: 700 },
  // Centroid for generated code
  CENTROID: { x: 960, y: 430 },
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  NOZZLE_BLUE: "#4A90D9",
  WALLS_AMBER: "#D9944A",
  GROUNDING_GREEN: "#5AAA6E",
  CODE_GRAY: "#A0A0A0",
  SUCCESS_GREEN: "#4CAF50",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Props schema
export const ThreeComponentsProps = z.object({
  showFormula: z.boolean().default(true),
});

export const defaultThreeComponentsProps: z.infer<typeof ThreeComponentsProps> = {
  showFormula: true,
};

export type ThreeComponentsPropsType = z.infer<typeof ThreeComponentsProps>;
