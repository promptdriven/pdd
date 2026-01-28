import { z } from "zod";

// Video specs from the animation doc
export const PIE_TO_CURVE_FPS = 30;
export const PIE_TO_CURVE_DURATION_SECONDS = 10;
export const PIE_TO_CURVE_DURATION_FRAMES = PIE_TO_CURVE_FPS * PIE_TO_CURVE_DURATION_SECONDS;
export const PIE_TO_CURVE_WIDTH = 1920;
export const PIE_TO_CURVE_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Frame 0-90: Morph begins - Pie chart rotates and flattens
// Frame 90-150: Axes establish - X/Y axes extend, grid lines fade in
// Frame 150-240: Curve draws - Exponential curve animates from origin
// Frame 240-300: Final state - Pulse animation, text fades in
export const BEATS = {
  MORPH_START: 0,
  MORPH_END: 90,              // 0-3s: Pie morphs into chart origin
  AXES_START: 90,
  AXES_END: 150,              // 3-5s: Axes establish with grid
  CURVE_START: 150,
  CURVE_END: 240,             // 5-8s: Exponential curve draws
  FINAL_START: 240,
  FINAL_END: 300,             // 8-10s: Final state with text
};

// Convert seconds to frames helper
export const secondsToFrames = (seconds: number) => Math.round(seconds * PIE_TO_CURVE_FPS);

// Color palette - maintaining amber continuity from pie segment
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  GRID: "#333344",
  AXIS: "#666677",
  AXIS_LABEL: "rgba(255, 255, 255, 0.8)",
  TEXT: "#ffffff",
  // Primary amber from pie segment
  AMBER: "#D9944A",
  // Faint blue for linear reference line
  LINEAR_REF: "rgba(74, 144, 217, 0.4)",
  // Pie chart colors for morph animation
  PIE_AMBER: "#D9944A",
  PIE_BLUE: "#4A90D9",
  PIE_GRAY: "#555566",
};

// Exponential cost curve data: y = 1.35^(year-1)
export const COST_CURVE_DATA = [
  { year: 1, cost: 1.0 },
  { year: 2, cost: 1.35 },
  { year: 3, cost: 1.82 },
  { year: 4, cost: 2.46 },
  { year: 5, cost: 3.32 },
  { year: 6, cost: 4.48 },
  { year: 7, cost: 6.05 },
  { year: 8, cost: 8.17 },
  { year: 9, cost: 11.03 },
  { year: 10, cost: 14.89 },
];

// Linear reference data (constant cost for comparison)
export const LINEAR_REF_DATA = [
  { year: 1, cost: 1.0 },
  { year: 10, cost: 1.0 },
];

// Chart dimensions (within the canvas)
export const CHART_MARGINS = {
  top: 120,
  right: 200,
  bottom: 150,
  left: 200,
};

export const YEAR_RANGE = { min: 1, max: 10 };
export const COST_RANGE = { min: 0, max: 16 };

// Pie chart initial state (for morph animation)
export const PIE_CONFIG = {
  centerX: 960,  // Center of 1920px
  centerY: 540,  // Center of 1080px
  radius: 200,
  // Segment representing the "growing cost" portion
  amberSegmentAngle: 120, // degrees
};

// Props schema
export const PieToCurveProps = z.object({
  showLinearRef: z.boolean().default(true),
});

export const defaultPieToCurveProps: z.infer<typeof PieToCurveProps> = {
  showLinearRef: true,
};

export type PieToCurvePropsType = z.infer<typeof PieToCurveProps>;

// Data point types
export interface CostDataPoint {
  year: number;
  cost: number;
}
