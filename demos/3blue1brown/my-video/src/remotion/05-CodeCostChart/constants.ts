import { z } from "zod";

// Video specs from the animation doc
export const CODE_CHART_FPS = 30;
export const CODE_CHART_DURATION_SECONDS = 20;
export const CODE_CHART_DURATION_FRAMES = CODE_CHART_FPS * CODE_CHART_DURATION_SECONDS;
export const CODE_CHART_WIDTH = 1920;
export const CODE_CHART_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Frame 0-90: Morphing transition (title changes to "The Economics of Code")
// Frame 90-150: New axes and title visible
// Frame 150-360: Chart draws 1970 → 2020
// Frame 360-480: 2020 → 2024 dramatic drop
// Frame 480-600: Hold
export const BEATS = {
  MORPH_START: 0,
  MORPH_END: 90,              // 0-3s: Morphing transition
  AXES_VISIBLE_START: 90,
  AXES_VISIBLE_END: 150,      // 3-5s: New axes and title visible
  DRAW_LINE_START: 150,
  DRAW_LINE_MID: 360,         // 5-12s: Chart draws 1970 → 2020
  DRAW_LINE_END: 480,         // 12-16s: 2020 → 2024 dramatic drop
  HOLD_START: 480,
  HOLD_END: 600,              // 16-20s: Hold
};

// Convert seconds to frames helper
export const secondsToFrames = (seconds: number) => Math.round(seconds * CODE_CHART_FPS);

// Color palette from spec
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  BACKGROUND_GRADIENT_END: "#0f0f1a",
  GRID: "#333344",
  AXIS: "#666677",
  AXIS_LABEL: "rgba(255, 255, 255, 0.8)",
  TITLE: "#ffffff",
  LINE_GENERATE: "#4A90D9",   // Blue - Cost to Generate
  LINE_PATCH: "#D9944A",      // Amber - Cost to Patch
};

// Chart data points
export const CHART_DATA = {
  costToGenerate: [
    { year: 1970, hours: 80 },
    { year: 1980, hours: 60 },
    { year: 1990, hours: 50 },
    { year: 2000, hours: 40 },
    { year: 2010, hours: 35 },
    { year: 2020, hours: 30 },
    { year: 2022, hours: 15 },
    { year: 2023, hours: 5 },
    { year: 2024, hours: 2 },
  ],
  costToPatch: [
    { year: 1970, hours: 5 },
    { year: 2000, hours: 8 },
    { year: 2024, hours: 12 },
  ],
};

// Chart dimensions (within the canvas)
export const CHART_MARGINS = {
  top: 100,
  right: 250,
  bottom: 120,
  left: 180,
};

export const YEAR_RANGE = { min: 1970, max: 2024 };
export const HOURS_RANGE = { min: 0, max: 100 };

// Props schema
export const CodeCostChartProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultCodeCostChartProps: z.infer<typeof CodeCostChartProps> = {
  showTitle: true,
};

export type CodeCostChartPropsType = z.infer<typeof CodeCostChartProps>;
