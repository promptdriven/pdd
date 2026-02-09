import { z } from "zod";

// Video specs
export const CODE_OUTPUT_FPS = 30;
export const CODE_OUTPUT_DURATION_SECONDS = 10;
export const CODE_OUTPUT_DURATION_FRAMES =
  CODE_OUTPUT_FPS * CODE_OUTPUT_DURATION_SECONDS;
export const CODE_OUTPUT_WIDTH = 1920;
export const CODE_OUTPUT_HEIGHT = 1080;

// Beat timings (in frames at 30fps) - aligned to spec
// Spec: Frame 0-60 (0-2s): Mold and plastic appear
// Spec: Frame 60-120 (2-4s): Mold glow intensifies
// Spec: Frame 120-180 (4-6s): First text line
// Spec: Frame 180-210 (6-7s): THE BEAT (one second of silence)
// Spec: Frame 210-270 (7-9s): Second text line + glow boost
// Spec: Frame 270-300 (9-10s): Final hold
export const BEATS = {
  MOLD_APPEAR_START: 0,
  MOLD_APPEAR_END: 45,
  PLASTIC_APPEAR_START: 15,
  PLASTIC_APPEAR_END: 50,
  MOLD_GLOW_INTENSIFY: 60,
  MESSAGE_1_START: 120,
  MESSAGE_1_END: 160,
  THE_BEAT_START: 180,
  THE_BEAT_END: 210,
  MESSAGE_2_START: 210,
  MESSAGE_2_END: 250,
  GLOW_BOOST_START: 210,
  GLOW_BOOST_END: 270,
  FINAL_HOLD: 270,
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
