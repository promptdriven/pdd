import { z } from "zod";

// Video specs
export const PROMPT_FLOW_FPS = 30;
export const PROMPT_FLOW_DURATION_SECONDS = 15;
export const PROMPT_FLOW_DURATION_FRAMES =
  PROMPT_FLOW_FPS * PROMPT_FLOW_DURATION_SECONDS;
export const PROMPT_FLOW_WIDTH = 1920;
export const PROMPT_FLOW_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  NOZZLE_START: 0,
  NOZZLE_END: 30,
  DOCUMENT_START: 0,
  DOCUMENT_PEAK: 60,
  DOCUMENT_FADE: 360,
  DOCUMENT_END: 420,
  LINE1_START: 90,
  LINE2_START: 180,
  LINE3_START: 270,
  TEXT_FLOW_START: 90,
  TEXT_FLOW_END: 360,
  TRANSFORM_START: 360,
  TRANSFORM_END: 450,
  HOLD_START: 400,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  NOZZLE_BLUE: "#4A90D9",
  TEXT_GLOW: "#4A90D9",
  CODE_GRAY: "#8a9caf",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Prompt text that flows
export const PROMPT_TEXT_LINES = [
  "Parse user IDs from untrusted input.",
  "Return None on failure, never throw.",
  "Handle unicode.",
];
export const PROMPT_TEXT = PROMPT_TEXT_LINES.join("\n");

// Props schema
export const PromptTextFlowsProps = z.object({
  promptText: z.string().default(PROMPT_TEXT),
});

export const defaultPromptTextFlowsProps: z.infer<typeof PromptTextFlowsProps> = {
  promptText: PROMPT_TEXT,
};

export type PromptTextFlowsPropsType = z.infer<typeof PromptTextFlowsProps>;
