import { z } from "zod";

// Video specs
export const RESEARCH_ANNOTATIONS_FPS = 30;
export const RESEARCH_ANNOTATIONS_DURATION_SECONDS = 15;
export const RESEARCH_ANNOTATIONS_DURATION_FRAMES =
  RESEARCH_ANNOTATIONS_FPS * RESEARCH_ANNOTATIONS_DURATION_SECONDS;
export const RESEARCH_ANNOTATIONS_WIDTH = 1920;
export const RESEARCH_ANNOTATIONS_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  WALLS_BASELINE: 0,
  CITATION1_START: 30,
  CITATION1_END: 120,
  EMPHASIS_FLASH_START: 60,
  EMPHASIS_FLASH_PEAK: 80,
  EMPHASIS_FLASH_END: 120,
  HOLD_BEFORE_CITATION2: 120,
  CITATION2_START: 150,
  CITATION2_END: 270,
  WALL_GLOW_START: 270,
  WALL_GLOW_END: 360,
  WALL_PULSE_START: 310,
  WALL_PULSE_END: 360,
  HOLD_BRIGHTENED: 360,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  WALLS_AMBER: "#D9944A",
  CITATION_MUTED: "#B0B0C0",
  CITATION_EMPHASIS: "#FFFFFF",
  WALLS_GLOW: "#D9944A",
};

// Citations
export const CITATIONS = {
  CODERABBIT: {
    MAIN: "AI code: 1.7x more issues",
    SOURCE: "(CodeRabbit, 2025)",
    EMPHASIS: "1.7x",
  },
  DORA: {
    MAIN: "AI + strong tests = amplified delivery",
    SOURCE: "(DORA, 2025)",
    EMPHASIS: "strong tests",
  },
};

// Layout positions
export const LAYOUT = {
  WALL_X: 400,
  WALL_Y: 540,
  WALL_WIDTH: 400,
  WALL_HEIGHT: 500,
  CITATION_X: 1100,
  CITATION1_Y: 340,
  CITATION2_Y: 480,
};

// Props schema
export const ResearchAnnotationsProps = z.object({
  showOverlay: z.boolean().default(true),
});

export const defaultResearchAnnotationsProps: z.infer<typeof ResearchAnnotationsProps> = {
  showOverlay: true,
};

export type ResearchAnnotationsPropsType = z.infer<typeof ResearchAnnotationsProps>;
