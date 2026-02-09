import { z } from "zod";

// Video specs
export const NOZZLE_FPS = 30;
export const NOZZLE_DURATION_SECONDS = 15;
export const NOZZLE_DURATION_FRAMES =
  NOZZLE_FPS * NOZZLE_DURATION_SECONDS;
export const NOZZLE_WIDTH = 1920;
export const NOZZLE_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  // Mold cross-section fade-in
  MOLD_START: 0,
  MOLD_END: 90,
  // Wall dimming
  WALL_DIM_START: 90,
  WALL_DIM_END: 150,
  // Nozzle glow
  NOZZLE_GLOW_START: 90,
  NOZZLE_GLOW_END: 180,
  // Concept labels (sequential)
  LABEL_INTENT_START: 180,
  LABEL_REQUIREMENTS_START: 240,
  LABEL_CONSTRAINTS_START: 300,
  LABEL_FADE_DURATION: 30,
  // Section title
  TITLE_START: 360,
  TITLE_END: 400,
  HOLD_START: 450,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  NOZZLE_BLUE: "#4A90D9",
  WALLS_AMBER: "#D9944A",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Concept labels configuration
export const CONCEPT_LABELS = [
  {
    text: "intent",
    description: "what you want",
    startFrame: 180,
    position: { x: -180, y: 80 }
  },
  {
    text: "requirements",
    description: "what it needs",
    startFrame: 240,
    position: { x: 200, y: 40 }
  },
  {
    text: "constraints",
    description: "boundaries",
    startFrame: 300,
    position: { x: 20, y: 160 }
  },
];

// Props schema
export const InjectionNozzleProps = z.object({
  showLabels: z.boolean().default(true),
});

export const defaultInjectionNozzleProps: z.infer<typeof InjectionNozzleProps> = {
  showLabels: true,
};

export type InjectionNozzlePropsType = z.infer<typeof InjectionNozzleProps>;
