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
  NOZZLE_START: 0,
  NOZZLE_END: 60,
  GLOW_START: 60,
  GLOW_END: 120,
  LABEL_START: 120,
  LABEL_END: 180,
  EXPLANATION_START: 210,
  HOLD_START: 360,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  NOZZLE_BLUE: "#4A90D9",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Props schema
export const InjectionNozzleProps = z.object({
  showLabels: z.boolean().default(true),
});

export const defaultInjectionNozzleProps: z.infer<typeof InjectionNozzleProps> = {
  showLabels: true,
};

export type InjectionNozzlePropsType = z.infer<typeof InjectionNozzleProps>;
