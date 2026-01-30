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
  SYSTEM_START: 0,
  SYSTEM_END: 90,
  PROMPT_GLOW_START: 120,
  PROMPT_GLOW_END: 180,
  GROUNDING_GLOW_START: 240,
  GROUNDING_GLOW_END: 300,
  WALLS_GLOW_START: 360,
  WALLS_GLOW_END: 420,
  CODE_OUTPUT_START: 480,
  CODE_OUTPUT_END: 540,
  FORMULA_START: 600,
  FORMULA_END: 660,
  HOLD_START: 720,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  NOZZLE_BLUE: "#4A90D9",
  WALLS_AMBER: "#D9944A",
  GROUNDING_GREEN: "#5AAA6E",
  CODE_GRAY: "#8a9caf",
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
