import { z } from "zod";

// Video specs
export const PROMPT_CODE_FPS = 30;
export const PROMPT_CODE_DURATION_SECONDS = 15;
export const PROMPT_CODE_DURATION_FRAMES =
  PROMPT_CODE_FPS * PROMPT_CODE_DURATION_SECONDS;
export const PROMPT_CODE_WIDTH = 1920;
export const PROMPT_CODE_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Frame 0-60:    Prompt activates — blue glow intensifies
// Frame 60-150:  Code flows from prompt — gray particles stream right/down
// Frame 150-270: Test walls materialize — amber bars appear one by one
// Frame 270-360: Code fills container — settles into final form
// Frame 360-450: Final state — prompt and walls glow, code is neutral
export const BEATS = {
  PROMPT_ACTIVATE_START: 0,
  PROMPT_ACTIVATE_END: 60,
  CODE_FLOW_START: 60,
  CODE_FLOW_END: 150,
  WALLS_START: 150,
  WALLS_END: 270,
  CODE_FILL_START: 270,
  CODE_FILL_END: 360,
  FINAL_START: 360,
  FINAL_END: 450,
  NARRATION_START: 360,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  PROMPT_BLUE: "#4A90D9",
  PROMPT_BLUE_GLOW: "rgba(74, 144, 217, 0.6)",
  TEST_AMBER: "#D9944A",
  TEST_AMBER_GLOW: "rgba(217, 148, 74, 0.6)",
  CODE_GRAY: "#A0A0A0",
  CODE_GRAY_DIM: "#707070",
  WHITE: "#ffffff",
  WHITE_DIM: "rgba(255, 255, 255, 0.7)",
};

// Prompt document configuration
export const PROMPT_DOC = {
  x: 120,
  y: 100,
  width: 300,
  height: 200,
  borderRadius: 8,
};

// Prompt text lines displayed inside the document
export const PROMPT_LINES = [
  "Convert input to Python",
  "null values -> None",
  "Ensure valid UTF-8",
  "Return formatted str",
];

// Test wall definitions
// Walls form a rectangular container in center-right of canvas
export interface TestWallDef {
  label: string;
  x: number;
  y: number;
  width: number;
  height: number;
  /** Frame at which this wall starts appearing */
  appearFrame: number;
}

export const TEST_WALLS: TestWallDef[] = [
  {
    label: "null \u2192 None",
    x: 620,
    y: 300,
    width: 780,
    height: 8,
    appearFrame: 150,
  },
  {
    label: "handles unicode",
    x: 1392,
    y: 300,
    width: 8,
    height: 408,
    appearFrame: 180,
  },
  {
    label: "no exceptions",
    x: 620,
    y: 700,
    width: 780,
    height: 8,
    appearFrame: 210,
  },
  {
    label: "valid format required",
    x: 620,
    y: 300,
    width: 8,
    height: 408,
    appearFrame: 240,
  },
];

// Container interior (area code fills)
export const CODE_CONTAINER = {
  x: 628,
  y: 308,
  width: 764,
  height: 392,
};

// Props schema
export const PromptGeneratesCodeProps = z.object({
  showNarration: z.boolean().default(true),
});

export const defaultPromptGeneratesCodeProps: z.infer<
  typeof PromptGeneratesCodeProps
> = {
  showNarration: true,
};

export type PromptGeneratesCodePropsType = z.infer<
  typeof PromptGeneratesCodeProps
>;
