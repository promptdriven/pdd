import { z } from "zod";

// Video specs (15 seconds at 30fps = 450 frames)
export const GRAPH_ANIMATE_FPS = 30;
export const GRAPH_ANIMATE_DURATION_SECONDS = 15;
export const GRAPH_ANIMATE_DURATION_FRAMES =
  GRAPH_ANIMATE_FPS * GRAPH_ANIMATE_DURATION_SECONDS;
export const GRAPH_ANIMATE_WIDTH = 1920;
export const GRAPH_ANIMATE_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  // Setup phase (0-2s)
  SETUP_START: 0,
  SETUP_END: 60,
  // Marker travels (2-10s)
  TRAVEL_START: 60,
  TRAVEL_END: 300,
  // Arrive at right (10-13s)
  ARRIVE_START: 300,
  ARRIVE_END: 390,
  // Emphasis (13-15s)
  EMPHASIS_START: 390,
  EMPHASIS_END: 450,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  NOZZLE_BLUE: "#4A90D9",
  WALLS_AMBER: "#D9944A",
  CURVE_CYAN: "#00BFFF",
  MARKER_WHITE: "#FFFFFF",
  LABEL_WHITE: "#ffffff",
  LABEL_GRAY: "#888888",
  AXIS_GRAY: "#555555",
};

// Props schema
export const GraphAnimateCurveProps = z.object({
  showLabels: z.boolean().default(true),
});

export const defaultGraphAnimateCurveProps: z.infer<typeof GraphAnimateCurveProps> = {
  showLabels: true,
};

export type GraphAnimateCurvePropsType = z.infer<typeof GraphAnimateCurveProps>;
