import { z } from "zod";

// Video specs
export const PRECISION_GRAPH_FPS = 30;
export const PRECISION_GRAPH_DURATION_SECONDS = 15;
export const PRECISION_GRAPH_DURATION_FRAMES =
  PRECISION_GRAPH_FPS * PRECISION_GRAPH_DURATION_SECONDS;
export const PRECISION_GRAPH_WIDTH = 1920;
export const PRECISION_GRAPH_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  // Axes appear (0-2s)
  Y_AXIS_START: 0,
  Y_AXIS_END: 60,
  X_AXIS_START: 20,
  X_AXIS_END: 80,
  // Labels fade in (2-4s)
  LABELS_START: 60,
  LABELS_END: 120,
  // Curve draws (4-9s)
  CURVE_START: 120,
  CURVE_END: 270,
  // Hold on complete graph (9-15s)
  HOLD_START: 270,
};

// Graph dimensions
export const GRAPH = {
  ORIGIN: { x: 200, y: 750 },
  Y_END: { x: 200, y: 150 },
  X_END: { x: 1700, y: 750 },
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  AXIS_COLOR: "rgba(255, 255, 255, 0.8)",
  LABEL_WHITE: "rgba(255, 255, 255, 0.9)",
  CURVE_BLUE: "#4A90D9",
  CURVE_AMBER: "#D9944A",
  REGION_LABEL: "rgba(255, 255, 255, 0.4)",
};

// Props schema
export const PrecisionGraphProps = z.object({
  showRegionLabels: z.boolean().default(true),
});

export const defaultPrecisionGraphProps: z.infer<typeof PrecisionGraphProps> = {
  showRegionLabels: true,
};

export type PrecisionGraphPropsType = z.infer<typeof PrecisionGraphProps>;
