import { z } from "zod";

// Video specs
export const PATCH_CYCLE_FPS = 30;
export const PATCH_CYCLE_DURATION_SECONDS = 10;
export const PATCH_CYCLE_DURATION_FRAMES =
  PATCH_CYCLE_FPS * PATCH_CYCLE_DURATION_SECONDS;
export const PATCH_CYCLE_WIDTH = 1920;
export const PATCH_CYCLE_HEIGHT = 1080;

// Color palette — matches CodeCostChart / CrossingPoint 3Blue1Brown style
export const COLORS = {
  BACKGROUND: "#0a0a1a",
  BACKGROUND_GRADIENT_END: "#0d1117",
  // Fork lines
  LINE_PATCH_SMALL: "#e8912d",   // same orange as LINE_PATCH in CodeCostChart
  LINE_PATCH_LARGE: "#e8912d",
  // Arrow and label
  ARROW: "#e8912d",
  LABEL_WHITE: "#ffffff",
  LABEL_DIM: "rgba(255, 255, 255, 0.55)",
  // Axis
  AXIS: "rgba(255, 255, 255, 0.25)",
  GRID: "rgba(255, 255, 255, 0.06)",
  // Glow zones
  GLOW_GREEN: "rgba(80, 200, 120, 0.12)",
  GLOW_RED: "rgba(220, 80, 80, 0.12)",
  ZONE_GREEN_BORDER: "rgba(80, 200, 120, 0.35)",
  ZONE_RED_BORDER: "rgba(220, 80, 80, 0.35)",
  ZONE_GREEN_TEXT: "rgba(80, 200, 120, 0.8)",
  ZONE_RED_TEXT: "rgba(220, 80, 80, 0.8)",
};

// Animation beat timing (frames at 30fps, relative to component start)
export const BEATS = {
  // Phase 1: Fork paths draw in
  FORK_DRAW_START: 0,
  FORK_DRAW_END: 90,         // 3s to draw both fork lines
  // Phase 2: Curved arrow draws in
  ARROW_DRAW_START: 75,      // slight overlap
  ARROW_DRAW_END: 150,       // 2.5s for the arrow
  // Phase 3: Label fades in
  LABEL_FADE_START: 130,
  LABEL_FADE_END: 170,
  // Phase 4: Zone labels fade in
  ZONES_FADE_START: 160,
  ZONES_FADE_END: 200,
};

// Props schema
export const PatchCycleProps = z.object({});

export const defaultPatchCycleProps: z.infer<typeof PatchCycleProps> = {};

export type PatchCyclePropsType = z.infer<typeof PatchCycleProps>;
