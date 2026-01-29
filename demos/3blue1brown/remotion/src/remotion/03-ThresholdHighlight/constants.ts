import { z } from "zod";

// Video specs from the animation doc
export const THRESHOLD_FPS = 30;
export const THRESHOLD_DURATION_SECONDS = 10;
export const THRESHOLD_DURATION_FRAMES = THRESHOLD_FPS * THRESHOLD_DURATION_SECONDS;
export const THRESHOLD_WIDTH = 1920;
export const THRESHOLD_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  MARKER_GROW_START: 0,
  MARKER_GROW_END: 30,           // 0-1s: Circle marker grows in
  LABEL_FADE_START: 60,
  LABEL_FADE_END: 120,           // 2-4s: Label fades in with connector line
  PULSE_1_START: 30,
  PULSE_1_END: 90,               // 1-3s: First pulse wave
  PULSE_2_START: 90,
  PULSE_2_END: 150,              // 3-5s: Second pulse wave
  PULSE_3_START: 150,
  PULSE_3_END: 210,              // 5-7s: Third pulse wave
  HOLD_START: 210,
  HOLD_END: 300,                 // 7-10s: Hold with subtle pulses
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
  PULSE_GLOW: "#D9944A",         // Amber glow
};

// Crossing point (where Cost to Buy = Cost to Repair at 0.5 hours)
// Based on the data: Cost to Buy at 1963 = 0.5, matching Cost to Repair
export const CROSSING_POINT = {
  year: 1963,
  hours: 0.5,
};

// Reuse chart constants from SockPriceChart
export const CHART_MARGINS = {
  top: 100,
  right: 250,
  bottom: 120,
  left: 180,
};

export const YEAR_RANGE = { min: 1950, max: 2020 };
export const HOURS_RANGE = { min: 0, max: 1.5 };

// Chart data (same as SockPriceChart - frozen state)
export const CHART_DATA = {
  costToBuy: [
    { year: 1950, hours: 1.0 },
    { year: 1955, hours: 0.75 },
    { year: 1960, hours: 0.55 },
    { year: 1963, hours: 0.5 },
    { year: 1970, hours: 0.2 },
    { year: 1980, hours: 0.1 },
    { year: 1990, hours: 0.06 },
    { year: 2000, hours: 0.04 },
    { year: 2010, hours: 0.03 },
    { year: 2020, hours: 0.03 },
  ],
  costToRepair: [
    { year: 1950, hours: 0.5 },
    { year: 2020, hours: 0.5 },
  ],
};

// Props schema
export const ThresholdHighlightProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultThresholdHighlightProps: z.infer<typeof ThresholdHighlightProps> = {
  showTitle: true,
};

export type ThresholdHighlightPropsType = z.infer<typeof ThresholdHighlightProps>;
