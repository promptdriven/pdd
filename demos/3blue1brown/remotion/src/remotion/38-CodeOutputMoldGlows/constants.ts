import { z } from "zod";

// Video specs
export const CODE_OUTPUT_FPS = 30;
export const CODE_OUTPUT_DURATION_SECONDS = 20;
export const CODE_OUTPUT_DURATION_FRAMES =
  CODE_OUTPUT_FPS * CODE_OUTPUT_DURATION_SECONDS;
export const CODE_OUTPUT_WIDTH = 1920;
export const CODE_OUTPUT_HEIGHT = 1080;

// Five-phase beat timings (in frames at 30fps) for standalone 20s version
// Phase 1 (0-4s):   Code glows brightly with "success" feeling
// Phase 2 (4-10s):  Code glow fades, code becomes gray and ordinary
// Phase 3 (10-14s): Mold components glow brighter, code clearly secondary
// Phase 4 (14-18s): "The code is output." message, code dim, mold strong
// Phase 5 (18-20s): "The mold is what matters." message, hold on glowing mold
export const BEATS = {
  // Phase 1: Code glows (frames 0-120)
  CODE_GLOW_HOLD_END: 120,

  // Phase 2: Code glow fades (frames 120-300)
  CODE_FADE_END: 300,

  // Phase 3: Mold prominence (frames 200-420)
  MOLD_GLOW_START: 200,
  MOLD_GLOW_END: 400,

  // Phase 4: First message (frames 420-460)
  MESSAGE_1_START: 420,
  MESSAGE_1_END: 460,

  // Phase 5: Second message (frames 540-580)
  MESSAGE_2_START: 540,
  MESSAGE_2_END: 580,

  // Total
  TOTAL_FRAMES: 600,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  PROMPT_BLUE: "#4A90D9",
  TESTS_AMBER: "#D9944A",
  GROUNDING_GREEN: "#5AAA6E",
  CODE_GRAY: "#A0A0A0",
  CODE_GLOW: "rgba(138, 156, 175, 0.5)",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Generated code - the parse_user_id Python function
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
  // Optional: override the total frame count used for animation scaling.
  // When the component is embedded in a shorter section, pass the available
  // frames so the five-phase animation compresses proportionally.
  durationFrames: z.number().optional(),
});

export const defaultCodeOutputMoldGlowsProps: z.infer<typeof CodeOutputMoldGlowsProps> = {
  showMessages: true,
};

export type CodeOutputMoldGlowsPropsType = z.infer<typeof CodeOutputMoldGlowsProps>;
