import { z } from "zod";

// Video specs
export const ENGINEER_FIXES_MOLD_FPS = 30;
export const ENGINEER_FIXES_MOLD_DURATION_SECONDS = 15;
export const ENGINEER_FIXES_MOLD_DURATION_FRAMES =
  ENGINEER_FIXES_MOLD_FPS * ENGINEER_FIXES_MOLD_DURATION_SECONDS;
export const ENGINEER_FIXES_MOLD_WIDTH = 1920;
export const ENGINEER_FIXES_MOLD_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  MOLD_APPEAR: 0,
  MOLD_VISIBLE: 60,
  TOOL_APPROACH: 90,
  TOOL_CONTACT: 150,
  ADJUSTMENT_START: 180,
  ADJUSTMENT_END: 270,
  SPARKS_START: 180,
  SPARKS_END: 270,
  SHAPE_CHANGE: 210,
  SHAPE_COMPLETE: 330,
  LABEL_APPEAR: 330,
  HOLD_START: 360,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  MOLD_GRAY: "#6a7988",
  MOLD_HIGHLIGHT: "#8a9caf",
  TOOL_METAL: "#b0bdc9",
  SPARK_YELLOW: "#FFD700",
  SPARK_ORANGE: "#FFA500",
  FIX_POINT_AMBER: "#D9944A",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Mold geometry
export const MOLD = {
  X: 960,
  Y: 540,
  WIDTH: 500,
  HEIGHT: 300,
  DEFECT_X: 720,
  DEFECT_Y: 400,
};

// Tool path
export const TOOL = {
  START_X: 1200,
  START_Y: 200,
  APPROACH_X: 750,
  APPROACH_Y: 420,
  CONTACT_X: 720,
  CONTACT_Y: 400,
};

// Props schema
export const EngineerFixesMoldProps = z.object({
  showOverlay: z.boolean().default(true),
});

export const defaultEngineerFixesMoldProps: z.infer<typeof EngineerFixesMoldProps> = {
  showOverlay: true,
};

export type EngineerFixesMoldPropsType = z.infer<typeof EngineerFixesMoldProps>;
