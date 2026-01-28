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
  LABEL_FADE_START: 30,
  LABEL_FADE_END: 60,            // 1-2s: Label fades in with connector (right after marker)
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

// Crossing point calculation (where Cost to Buy ≈ Cost to Repair at 0.5 hours)
// Based on the data: Cost to Buy at 1970 = 1.0, at 1980 = 0.4
// Linear interpolation: 0.5 = 1.0 + (year - 1970) * (0.4 - 1.0) / 10
// Solving: year = 1970 + (1.0 - 0.5) * 10 / 0.6 = 1978.33
export const CROSSING_POINT = {
  year: 1978.33,
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
export const HOURS_RANGE = { min: 0, max: 3 };

// Chart data (same as SockPriceChart - frozen state)
export const CHART_DATA = {
  costToBuy: [
    { year: 1950, hours: 2.5 },
    { year: 1960, hours: 1.8 },
    { year: 1970, hours: 1.0 },
    { year: 1980, hours: 0.4 },
    { year: 1990, hours: 0.15 },
    { year: 2000, hours: 0.08 },
    { year: 2010, hours: 0.05 },
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
