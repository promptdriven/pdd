import { z } from "zod";

// Video specs from the animation doc
export const SOCK_CHART_FPS = 30;
export const SOCK_CHART_DURATION_SECONDS = 20;
export const SOCK_CHART_DURATION_FRAMES = SOCK_CHART_FPS * SOCK_CHART_DURATION_SECONDS;
export const SOCK_CHART_WIDTH = 1920;
export const SOCK_CHART_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  AXES_FADE_IN_START: 0,
  AXES_FADE_IN_END: 30,       // 0-1s
  BUY_LINE_START: 30,
  BUY_LINE_END: 90,           // 1-3s
  REPAIR_LINE_START: 90,
  REPAIR_LINE_END: 150,       // 3-5s
  TIME_PROGRESS_START: 150,
  TIME_PROGRESS_END: 300,     // 5-10s
  DROP_START: 300,
  DROP_END: 450,              // 10-15s
  APPROACH_START: 450,
  APPROACH_END: 540,          // 15-18s
  HOLD_START: 540,
  HOLD_END: 600,              // 18-20s
};

// Convert seconds to frames helper
export const secondsToFrames = (seconds: number) => Math.round(seconds * SOCK_CHART_FPS);

// Color palette from spec
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  BACKGROUND_GRADIENT_END: "#0f0f1a",
  GRID: "#333344",
  AXIS: "#666677",
  AXIS_LABEL: "rgba(255, 255, 255, 0.8)",
  TITLE: "#ffffff",
  LINE_BUY: "#4A90D9",      // Cool blue - Cost to Buy
  LINE_REPAIR: "#D9944A",   // Warm amber - Cost to Repair
};

// Chart data points
export const CHART_DATA = {
  costToBuy: [
    { year: 1920, hours: 1.4 },
    { year: 1930, hours: 1.3 },
    { year: 1940, hours: 1.2 },
    { year: 1950, hours: 1.0 },
    { year: 1955, hours: 0.75 },
    { year: 1960, hours: 0.55 },
    { year: 1963, hours: 0.5 },
    { year: 1970, hours: 0.2 },
    { year: 1980, hours: 0.1 },
    { year: 1990, hours: 0.06 },
  ],
  costToRepair: [
    { year: 1920, hours: 0.5 },
    { year: 1990, hours: 0.5 },
  ],
};

// Chart dimensions (within the canvas)
export const CHART_MARGINS = {
  top: 100,
  right: 250,
  bottom: 120,
  left: 180,
};

export const YEAR_RANGE = { min: 1920, max: 1990 };
export const HOURS_RANGE = { min: 0, max: 1.5 };

// Props schema
export const SockPriceChartProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultSockPriceChartProps: z.infer<typeof SockPriceChartProps> = {
  showTitle: true,
};

export type SockPriceChartPropsType = z.infer<typeof SockPriceChartProps>;
