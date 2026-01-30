import { z } from "zod";

// Video specs
export const LIQUID_INJECTION_FPS = 30;
export const LIQUID_INJECTION_DURATION_SECONDS = 20;
export const LIQUID_INJECTION_DURATION_FRAMES =
  LIQUID_INJECTION_FPS * LIQUID_INJECTION_DURATION_SECONDS;
export const LIQUID_INJECTION_WIDTH = 1920;
export const LIQUID_INJECTION_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  MOLD_START: 0,
  MOLD_END: 30,
  INJECTION_START: 30,
  FILL_PROGRESS: 180, // Frame where fill completes
  WALL_CONTACT_START: 90,
  WALL_CONTACT_END: 180,
  CODE_START: 200,
  CODE_COMPLETE: 360,
  CHECKMARK_START: 400,
  HOLD_START: 480,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  WALLS_AMBER: "#D9944A",
  NOZZLE_BLUE: "#4A90D9",
  MATERIAL_GREEN: "#5AAA6E",
  CODE_GRAY: "#8a9caf",
  OUTLINE_GRAY: "#5a6a7a",
  LABEL_WHITE: "#ffffff",
  SUCCESS_GREEN: "#4CAF50",
};

// Mold configuration
export const MOLD = {
  centerX: 960,
  centerY: 480,
  width: 500,
  height: 350,
  wallThickness: 40,
  nozzleWidth: 60,
  nozzleHeight: 50,
};

// Code that will be "generated"
export const GENERATED_CODE = `def parse_user_id(input_str):
    if not input_str or not input_str.strip():
        return None
    cleaned = input_str.strip()
    if not cleaned.isalnum():
        return None
    return cleaned`;

// Props schema
export const LiquidInjectionProps = z.object({
  showCode: z.boolean().default(true),
});

export const defaultLiquidInjectionProps: z.infer<typeof LiquidInjectionProps> = {
  showCode: true,
};

export type LiquidInjectionPropsType = z.infer<typeof LiquidInjectionProps>;
