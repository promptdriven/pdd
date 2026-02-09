import { z } from "zod";

// Video specs
export const PATCH_CYCLE_FPS = 30;
export const PATCH_CYCLE_DURATION_SECONDS = 10;
export const PATCH_CYCLE_DURATION_FRAMES =
  PATCH_CYCLE_FPS * PATCH_CYCLE_DURATION_SECONDS;
export const PATCH_CYCLE_WIDTH = 1920;
export const PATCH_CYCLE_HEIGHT = 1080;

// The Veo 3.1 video file name — replace once the asset is generated
export const PATCH_CYCLE_VIDEO_FILE = "veo_patch_cycle.mp4";

// Color palette
export const COLORS = {
  BACKGROUND: "#0a0a1a",
  BACKGROUND_GRADIENT: "#0d1117",
  // Placeholder text
  LABEL_WHITE: "rgba(255, 255, 255, 0.85)",
  LABEL_DIM: "rgba(255, 255, 255, 0.4)",
  // Monitor glow effect for placeholder
  MONITOR_BLUE: "rgba(70, 130, 220, 0.15)",
  ACCENT_BLUE: "#4682dc",
};

// Props schema
export const PatchCycleProps = z.object({
  /** When true, show placeholder instead of video (for when video asset is missing) */
  usePlaceholder: z.boolean().default(true),
});

export const defaultPatchCycleProps: z.infer<typeof PatchCycleProps> = {
  usePlaceholder: true,
};

export type PatchCyclePropsType = z.infer<typeof PatchCycleProps>;
