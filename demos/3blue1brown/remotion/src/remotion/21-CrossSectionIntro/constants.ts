import { z } from "zod";

// Video specs
export const CROSS_SECTION_FPS = 30;
export const CROSS_SECTION_DURATION_SECONDS = 15;
export const CROSS_SECTION_DURATION_FRAMES =
  CROSS_SECTION_FPS * CROSS_SECTION_DURATION_SECONDS;
export const CROSS_SECTION_WIDTH = 1920;
export const CROSS_SECTION_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  OUTLINE_START: 0,
  OUTLINE_END: 90,
  WALLS_START: 90,
  WALLS_END: 150,
  NOZZLE_START: 150,
  NOZZLE_END: 210,
  MATERIAL_START: 210,
  MATERIAL_END: 270,
  ALL_VISIBLE_END: 450,
};

// Color palette - PDD theme colors
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  WALLS_AMBER: "#D9944A",
  NOZZLE_BLUE: "#4A90D9",
  MATERIAL_GREEN: "#5AAA6E",
  OUTLINE_GRAY: "#5a6a7a",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Mold cross-section configuration
export const MOLD = {
  centerX: 960,
  centerY: 500,
  outerWidth: 600,
  outerHeight: 400,
  wallThickness: 40,
  nozzleWidth: 80,
  nozzleHeight: 60,
};

// Props schema
export const CrossSectionIntroProps = z.object({
  showLabels: z.boolean().default(true),
});

export const defaultCrossSectionIntroProps: z.infer<typeof CrossSectionIntroProps> = {
  showLabels: true,
};

export type CrossSectionIntroPropsType = z.infer<typeof CrossSectionIntroProps>;
