import { z } from "zod";

// Video specs from the animation doc
export const PIE_CHART_FPS = 30;
export const PIE_CHART_DURATION_SECONDS = 15;
export const PIE_CHART_DURATION_FRAMES = PIE_CHART_FPS * PIE_CHART_DURATION_SECONDS; // 450 frames
export const PIE_CHART_WIDTH = 1920;
export const PIE_CHART_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Frame 0-60: Previous content fades out
// Frame 60-120: Pie chart base appears (circle outline)
// Frame 120-180: Blue segment draws clockwise (small arc ~55°)
// Frame 180-300: Amber segment draws clockwise (enormous arc to 360°)
// Frame 300-360: Percentages fade in
// Frame 360-450: Hold with subtle pulse on maintenance segment
export const BEATS = {
  FADE_OUT_START: 0,
  FADE_OUT_END: 60,
  BASE_APPEAR_START: 60,
  BASE_APPEAR_END: 120,
  BLUE_SEGMENT_START: 120,
  BLUE_SEGMENT_END: 180,
  AMBER_SEGMENT_START: 180,
  AMBER_SEGMENT_END: 300,
  PERCENTAGES_START: 300,
  PERCENTAGES_END: 360,
  PULSE_START: 360,
  PULSE_END: 450,
};

// Convert seconds to frames helper
export const secondsToFrames = (seconds: number) => Math.round(seconds * PIE_CHART_FPS);

// Color palette from spec
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  INITIAL_DEVELOPMENT: "#4A90D9",  // Cool blue
  MAINTENANCE: "#D9944A",          // Warm amber
  TITLE: "#ffffff",
  LABEL: "#ffffff",
  STROKE: "#ffffff",
};

// Pie chart segment data
export const PIE_SEGMENTS = {
  initialDevelopment: {
    percentage: 15,                    // 15% of the pie
    startAngle: 0,                     // Start from 12 o'clock (0° = top)
    endAngle: 54,                      // ~55° arc (15% of 360°)
    color: COLORS.INITIAL_DEVELOPMENT,
    label: "Initial Development",
    percentageLabel: "10-20%",
  },
  maintenance: {
    percentage: 85,                    // 85% of the pie
    startAngle: 54,                    // Start where blue ends
    endAngle: 360,                     // Full circle
    color: COLORS.MAINTENANCE,
    label: "Maintenance",
    percentageLabel: "80-90%",
  },
};

// Chart dimensions
export const CHART_CENTER = {
  x: PIE_CHART_WIDTH / 2,
  y: PIE_CHART_HEIGHT / 2 + 20,        // Slightly below center to account for title
};

export const CHART_RADIUS = 280;        // Main pie radius
export const SEGMENT_GAP = 3;           // Gap between segments in pixels
export const STROKE_WIDTH = 1;          // White stroke width

// Props schema
export const PieChartProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultPieChartProps: z.infer<typeof PieChartProps> = {
  showTitle: true,
};

export type PieChartPropsType = z.infer<typeof PieChartProps>;
