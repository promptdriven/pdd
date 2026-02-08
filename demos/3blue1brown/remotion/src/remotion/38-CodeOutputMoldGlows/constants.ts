import { z } from "zod";

// Video specs
export const CODE_OUTPUT_FPS = 30;
export const CODE_OUTPUT_DURATION_SECONDS = 20;
export const CODE_OUTPUT_DURATION_FRAMES =
  CODE_OUTPUT_FPS * CODE_OUTPUT_DURATION_SECONDS;
export const CODE_OUTPUT_WIDTH = 1920;
export const CODE_OUTPUT_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  CODE_GLOW_START: 0,
  CODE_GLOW_PEAK: 120,
  CODE_GLOW_FADE: 300,
  MOLD_GLOW_START: 200,
  MOLD_GLOW_PEAK: 400,
  MESSAGE_1_START: 420,
  MESSAGE_1_END: 460,
  MESSAGE_2_START: 540,
  MESSAGE_2_END: 580,
  HOLD_START: 560,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  NOZZLE_BLUE: "#4A90D9",
  WALLS_AMBER: "#D9944A",
  GROUNDING_GREEN: "#5AAA6E",
  CODE_GRAY: "#A0A0A0",
  CODE_GLOW: "rgba(138, 156, 175, 0.5)",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Generated code
export const GENERATED_CODE = `def parse_user_id(input_str):
    """Parse user ID from untrusted input."""
    if not input_str or not input_str.strip():
        return None
    cleaned = input_str.strip()
    if not cleaned.isalnum():
        return None
    return cleaned`;

// Props schema
export const CodeOutputMoldGlowsProps = z.object({
  showMessages: z.boolean().default(true),
});

export const defaultCodeOutputMoldGlowsProps: z.infer<typeof CodeOutputMoldGlowsProps> = {
  showMessages: true,
};

export type CodeOutputMoldGlowsPropsType = z.infer<typeof CodeOutputMoldGlowsProps>;
