import { z } from "zod";

// Video specs
export const VALUE_AURA_FPS = 30;
export const VALUE_AURA_DURATION_SECONDS = 15;
export const VALUE_AURA_DURATION_FRAMES =
  VALUE_AURA_FPS * VALUE_AURA_DURATION_SECONDS;
export const VALUE_AURA_WIDTH = 1920;
export const VALUE_AURA_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Frame 0-90:    Split screen holds, subtle preparation
// Frame 90-180:  Left aura fades in around the chair (object glows)
// Frame 180-270: Right aura fades in around the mold (mold glows, parts do NOT)
// Frame 270-360: Both auras visible, pulsing in sync
// Frame 360-450: Labels fade in, hold to end
export const BEATS = {
  PREPARE_START: 0,
  PREPARE_END: 90,
  LEFT_AURA_START: 90,
  LEFT_AURA_END: 180,
  RIGHT_AURA_START: 180,
  RIGHT_AURA_END: 270,
  BOTH_PULSE_START: 270,
  BOTH_PULSE_END: 360,
  LABELS_START: 360,
  LABELS_END: 450,
  NARRATION_1_START: 90,
  NARRATION_2_START: 270,
};

// Color palette
export const COLORS = {
  // Left side (crafted object / warm)
  LEFT_BG: "#2e2218",
  LEFT_BG_GRADIENT_END: "#1f170f",

  // Right side (mold / dark industrial)
  RIGHT_BG: "#1a1a2e",
  RIGHT_BG_GRADIENT_END: "#0f0f1a",

  // Aura
  AURA_WHITE: "#ffffff",
  AURA_GOLD: "#FFD700",
  AURA_GOLD_LIGHT: "rgba(255, 215, 0, 0.4)",

  // Chair
  CHAIR_WOOD: "#8B6914",
  CHAIR_WOOD_DARK: "#5C4510",
  CHAIR_WOOD_LIGHT: "#A67C2E",

  // Mold
  MOLD_BODY: "#5a6a7a",
  MOLD_EDGE: "#8a9aaa",
  MOLD_CAVITY: "#2a2a3e",
  MOLD_METALLIC_LIGHT: "#7a8a9a",
  MOLD_METALLIC_DARK: "#4a5a6a",

  // Parts (amber, NOT glowing)
  PART_AMBER: "#D9944A",
  PART_AMBER_DIM: "#9e6b35",

  // Divider
  DIVIDER: "rgba(255, 255, 255, 0.2)",

  // Labels
  LABEL_WHITE: "#ffffff",
};

// Props schema
export const ValueAuraProps = z.object({
  showNarration: z.boolean().default(true),
});

export const defaultValueAuraProps: z.infer<typeof ValueAuraProps> = {
  showNarration: true,
};

export type ValueAuraPropsType = z.infer<typeof ValueAuraProps>;
