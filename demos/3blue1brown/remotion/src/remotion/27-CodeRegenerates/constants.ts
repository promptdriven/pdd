import { z } from "zod";

// Video specs
export const CODE_REGEN_FPS = 30;
export const CODE_REGEN_DURATION_SECONDS = 20;
export const CODE_REGEN_DURATION_FRAMES =
  CODE_REGEN_FPS * CODE_REGEN_DURATION_SECONDS;
export const CODE_REGEN_WIDTH = 1920;
export const CODE_REGEN_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  OLD_CODE_START: 0,
  OLD_CODE_END: 60,
  DISSOLVE_START: 90,
  DISSOLVE_END: 180,
  REGENERATE_START: 210,
  REGENERATE_END: 390,
  NEW_CODE_GLOW_START: 390,
  NEW_CODE_GLOW_END: 450,
  CHECKMARK_START: 480,
  HOLD_START: 540,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  CODE_GRAY: "#8a9caf",
  SUCCESS_GREEN: "#4CAF50",
  DISSOLVE_ORANGE: "#D9944A",
  LABEL_WHITE: "#ffffff",
};

// Old buggy code
export const OLD_CODE = `def parse_user_id(input_str):
    if not input_str:
        return None
    cleaned = input_str  # Missing .strip()!
    if not cleaned.isalnum():
        return None
    return cleaned`;

// New fixed code
export const NEW_CODE = `def parse_user_id(input_str):
    if not input_str or not input_str.strip():
        return None
    cleaned = input_str.strip()
    if not cleaned.isalnum():
        return None
    return cleaned`;

// Props schema
export const CodeRegeneratesProps = z.object({
  showTransition: z.boolean().default(true),
});

export const defaultCodeRegeneratesProps: z.infer<typeof CodeRegeneratesProps> = {
  showTransition: true,
};

export type CodeRegeneratesPropsType = z.infer<typeof CodeRegeneratesProps>;
