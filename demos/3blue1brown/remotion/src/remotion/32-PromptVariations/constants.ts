import { z } from "zod";

// Video specs
export const PROMPT_VARIATIONS_FPS = 30;
export const PROMPT_VARIATIONS_DURATION_SECONDS = 20;
export const PROMPT_VARIATIONS_DURATION_FRAMES =
  PROMPT_VARIATIONS_FPS * PROMPT_VARIATIONS_DURATION_SECONDS;
export const PROMPT_VARIATIONS_WIDTH = 1920;
export const PROMPT_VARIATIONS_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  PROMPT_START: 0,
  PROMPT_END: 60,
  VARIATION_1_START: 90,
  VARIATION_2_START: 180,
  VARIATION_3_START: 270,
  INSIGHT_START: 420,
  HOLD_START: 540,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  NOZZLE_BLUE: "#4A90D9",
  CODE_GRAY: "#8a9caf",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Same prompt with variations in output
export const BASE_PROMPT = "Parse user ID from input";

export const VARIATIONS = [
  {
    label: "Run 1",
    code: `def parse_user_id(s):
    return s.strip() if s else None`,
  },
  {
    label: "Run 2",
    code: `def parse_user_id(input_str):
    if not input_str:
        return None
    return input_str.strip()`,
  },
  {
    label: "Run 3",
    code: `def parse_user_id(value):
    cleaned = (value or "").strip()
    return cleaned or None`,
  },
];

// Props schema
export const PromptVariationsProps = z.object({
  showVariations: z.boolean().default(true),
});

export const defaultPromptVariationsProps: z.infer<typeof PromptVariationsProps> = {
  showVariations: true,
};

export type PromptVariationsPropsType = z.infer<typeof PromptVariationsProps>;
