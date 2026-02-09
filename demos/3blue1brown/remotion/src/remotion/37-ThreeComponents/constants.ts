import { z } from "zod";

// Video specs
export const THREE_COMPONENTS_FPS = 30;
export const THREE_COMPONENTS_DURATION_SECONDS = 25;
export const THREE_COMPONENTS_DURATION_FRAMES =
  THREE_COMPONENTS_FPS * THREE_COMPONENTS_DURATION_SECONDS;
export const THREE_COMPONENTS_WIDTH = 1920;
export const THREE_COMPONENTS_HEIGHT = 1080;

// Triangle geometry (spec: centerX=960, centerY=480, radius=280)
const CENTER_X = 960;
const CENTER_Y = 480;
const RADIUS = 280;

export const LAYOUT = {
  CENTER_X,
  CENTER_Y,
  RADIUS,
  // Vertex positions (equilateral triangle)
  PROMPT: { x: CENTER_X, y: CENTER_Y - RADIUS }, // (960, 200)
  TESTS: {
    x: Math.round(CENTER_X - RADIUS * 0.866),
    y: Math.round(CENTER_Y + RADIUS * 0.5),
  }, // (~718, 620)
  GROUNDING: {
    x: Math.round(CENTER_X + RADIUS * 0.866),
    y: Math.round(CENTER_Y + RADIUS * 0.5),
  }, // (~1202, 620)
  // Geometric centroid: average of the three vertex positions
  // = (CENTER_Y - R + CENTER_Y + R*0.5 + CENTER_Y + R*0.5) / 3 = CENTER_Y
  CENTROID: {
    x: CENTER_X,
    y: Math.round(
      ((CENTER_Y - RADIUS) + (CENTER_Y + RADIUS * 0.5) + (CENTER_Y + RADIUS * 0.5)) / 3
    ),
  }, // (960, 480)
};

// Beat timings (in frames at 30fps)
// Spec animation sequence: vertices 0-60, edges 60-120, glow+sublabels 120-180, code 180-240, hold 240-300
//
// Per-vertex narration pulse sync (in ClosingSection context, ThreeComponents starts at 13.02s):
//   "Prompts encode intent"     -> local frame ~0   (13.0s)
//   "Tests preserve behavior"   -> local frame ~68  (15.3s)
//   "Grounding maintains style" -> local frame ~131 (17.4s)
export const BEATS = {
  // Phase 1: Vertex staggered appearance (0-60)
  VERTEX_PROMPT_DELAY: 0,
  VERTEX_TESTS_DELAY: 10,
  VERTEX_GROUNDING_DELAY: 20,
  VERTEX_SCALE_DURATION: 30,

  // Phase 2: Edge drawing (60-120)
  EDGES_START: 60,
  EDGES_END: 120,

  // Phase 3: Glow intensification + sub-labels (120-180)
  // Per-vertex narration pulse timing (staggered)
  GLOW_PROMPT_START: 120,
  GLOW_PROMPT_END: 140,
  GLOW_TESTS_START: 135,
  GLOW_TESTS_END: 155,
  GLOW_GROUNDING_START: 150,
  GLOW_GROUNDING_END: 170,

  // Sub-label fade-in (spec: frames 130-170)
  SUBLABEL_START: 130,
  SUBLABEL_END: 170,

  // Phase 4: Center code appearance (180-240)
  CODE_START: 180,
  CODE_END: 220,

  // Derivation arrows (200-240)
  ARROWS_START: 200,
  ARROWS_END: 240,

  // Phase 5: Hold (240-300)
  HOLD_START: 240,

  // Integration formula (standalone only, never reached in closing context)
  FORMULA_START: 600,
  FORMULA_END: 660,
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

// Vertex definitions
export const VERTICES = {
  prompt: {
    label: "PROMPT",
    sublabel: "encodes intent",
    color: COLORS.NOZZLE_BLUE,
    ...LAYOUT.PROMPT,
  },
  tests: {
    label: "TESTS",
    sublabel: "preserves behavior",
    color: COLORS.WALLS_AMBER,
    ...LAYOUT.TESTS,
  },
  grounding: {
    label: "GROUNDING",
    sublabel: "maintains style",
    color: COLORS.GROUNDING_GREEN,
    ...LAYOUT.GROUNDING,
  },
};

// Edge definitions (pairs of vertex keys)
export const EDGES: Array<[keyof typeof VERTICES, keyof typeof VERTICES]> = [
  ["prompt", "tests"],
  ["tests", "grounding"],
  ["grounding", "prompt"],
];

// Props schema
export const ThreeComponentsProps = z.object({
  showFormula: z.boolean().default(true),
});

export const defaultThreeComponentsProps: z.infer<typeof ThreeComponentsProps> = {
  showFormula: true,
};

export type ThreeComponentsPropsType = z.infer<typeof ThreeComponentsProps>;
