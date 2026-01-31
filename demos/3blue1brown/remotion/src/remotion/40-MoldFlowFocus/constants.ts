import { z } from "zod";

// Video specs (15 seconds at 30fps)
export const MOLD_FLOW_FOCUS_FPS = 30;
export const MOLD_FLOW_FOCUS_DURATION_SECONDS = 15;
export const MOLD_FLOW_FOCUS_DURATION_FRAMES =
  MOLD_FLOW_FOCUS_FPS * MOLD_FLOW_FOCUS_DURATION_SECONDS;
export const MOLD_FLOW_FOCUS_WIDTH = 1920;
export const MOLD_FLOW_FOCUS_HEIGHT = 1080;

// Beat timings (in frames at 30fps) - from spec
export const BEATS = {
  // Frame 0-90 (0-3s): Wall highlights fade in
  WALL_GLOW_START: 0,
  WALL_GLOW_END: 90,
  // Frame 90-180 (3-6s): Flow contacts walls
  CONTACT_1_START: 90,
  CONTACT_2_START: 150,
  CONTACT_3_START: 210,
  // Frame 180-300 (6-10s): Walls constrain flow
  CONSTRAIN_START: 180,
  CONSTRAIN_END: 300,
  // Frame 300-450 (10-15s): Label appears
  LABEL_START: 300,
  LABEL_END: 360,
  HOLD_START: 360,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  WALLS_AMBER: "#D9944A",
  LIQUID_BLUE: "#4A90D9",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
};

// Contact point positions for wall glow pulses
export const CONTACT_POINTS = [
  { x: 300, y: 400 },
  { x: 800, y: 350 },
  { x: 550, y: 600 },
];

// Props schema
export const MoldFlowFocusProps = z.object({
  showLabel: z.boolean().default(true),
});

export const defaultMoldFlowFocusProps: z.infer<typeof MoldFlowFocusProps> = {
  showLabel: true,
};

export type MoldFlowFocusPropsType = z.infer<typeof MoldFlowFocusProps>;
