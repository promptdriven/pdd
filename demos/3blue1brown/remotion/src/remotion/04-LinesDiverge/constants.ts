import { z } from "zod";

// Video specs from the animation doc
export const LINES_DIVERGE_FPS = 30;
export const LINES_DIVERGE_DURATION_SECONDS = 15;
export const LINES_DIVERGE_DURATION_FRAMES = LINES_DIVERGE_FPS * LINES_DIVERGE_DURATION_SECONDS; // 450 frames
export const LINES_DIVERGE_WIDTH = 1920;
export const LINES_DIVERGE_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  // Threshold marker fades to 50%
  THRESHOLD_FADE_START: 0,
  THRESHOLD_FADE_END: 60,            // 0-2s: Threshold fades to 50%

  // Time progress and Cost to Buy line drops
  TIME_PROGRESS_START: 0,
  TIME_PROGRESS_END: 270,             // 0-9s: Year 1980 -> 2020, line drops

  // Shaded irrational zone fades in
  SHADED_REGION_FADE_START: 120,
  SHADED_REGION_FADE_END: 180,        // 4-6s: Shaded region fades in

  // Gap indicator appears
  GAP_INDICATOR_START: 180,
  GAP_INDICATOR_END: 270,             // 6-9s: Gap indicator appears

  // Hold on final state
  HOLD_START: 270,
  HOLD_END: 360,                      // 9-12s: Hold

  // Slight zoom out
  ZOOM_OUT_START: 360,
  ZOOM_OUT_END: 450,                  // 12-15s: Zoom out
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  BACKGROUND_GRADIENT_END: "#0f0f1a",
  GRID: "#333344",
  AXIS: "#666677",
  AXIS_LABEL: "rgba(255, 255, 255, 0.8)",
  TITLE: "#ffffff",
  LINE_BUY: "#4A90D9",
  LINE_REPAIR: "#D9944A",
  MARKER: "#FFFFFF",
  PULSE_GLOW: "#D9944A",
  IRRATIONAL_ZONE: "rgba(217, 148, 74, 0.2)",  // Semi-transparent amber
  GAP_INDICATOR: "#E74C3C",  // Red for emphasis
};

// Crossing point (threshold) from previous section
export const CROSSING_POINT = {
  year: 1978.33,
  hours: 0.5,
};

// Chart constants
export const CHART_MARGINS = {
  top: 100,
  right: 250,
  bottom: 120,
  left: 180,
};

export const YEAR_RANGE = { min: 1950, max: 2020 };
export const HOURS_RANGE = { min: 0, max: 3 };

// Chart data - Cost to Buy continues to drop dramatically
// For this section, we animate from 1980 onwards
export const CHART_DATA = {
  // Full data for complete line display
  costToBuyFull: [
    { year: 1950, hours: 2.5 },
    { year: 1960, hours: 1.8 },
    { year: 1970, hours: 1.0 },
    { year: 1980, hours: 0.4 },
    { year: 1990, hours: 0.15 },
    { year: 2000, hours: 0.08 },
    { year: 2010, hours: 0.05 },
    { year: 2020, hours: 0.03 },
  ],
  // Data from 1980 onwards for animation
  costToBuyFrom1980: [
    { year: 1980, hours: 0.4 },
    { year: 1990, hours: 0.15 },
    { year: 2000, hours: 0.08 },
    { year: 2010, hours: 0.05 },
    { year: 2020, hours: 0.03 },
  ],
  // Static repair line
  costToRepair: [
    { year: 1950, hours: 0.5 },
    { year: 2020, hours: 0.5 },
  ],
  // Pre-1980 data (frozen from threshold section)
  costToBuyUntil1980: [
    { year: 1950, hours: 2.5 },
    { year: 1960, hours: 1.8 },
    { year: 1970, hours: 1.0 },
    { year: 1980, hours: 0.4 },
  ],
};

// Year counter config
export const YEAR_COUNTER = {
  startYear: 1980,
  endYear: 2020,
};

// Props schema
export const LinesDivergeProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultLinesDivergeProps: z.infer<typeof LinesDivergeProps> = {
  showTitle: true,
};

export type LinesDivergePropsType = z.infer<typeof LinesDivergeProps>;
