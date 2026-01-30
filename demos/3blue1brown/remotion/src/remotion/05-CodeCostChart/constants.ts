import { z } from "zod";

// Video specs from the animation doc
export const CODE_CHART_FPS = 30;
export const CODE_CHART_DURATION_SECONDS = 120;
export const CODE_CHART_DURATION_FRAMES = CODE_CHART_FPS * CODE_CHART_DURATION_SECONDS;
export const CODE_CHART_WIDTH = 1920;
export const CODE_CHART_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
// Frame 0-540: Morphing transition (title changes to "The Economics of Code")
// Frame 540-900: New axes and title visible
// Frame 900-2160: Chart draws 1970 -> 2020
// Frame 2160-2880: 2020 -> 2025 dramatic drop (THE KEY MOMENT)
// Frame 2880-3240: Emphasis beat with annotations
// Frame 3240-3600: Crossing point emphasis
export const BEATS = {
  MORPH_START: 0,
  MORPH_END: 540,              // 0-18s: Morphing transition
  AXES_VISIBLE_START: 540,
  AXES_VISIBLE_END: 750,       // 18-25s: New axes and title visible
  DRAW_LINE_START: 750,
  DRAW_LINE_MID: 1500,         // 25-50s: Chart draws 2015 -> 2020
  DRAW_LINE_END: 2700,         // 50-90s: 2020 -> 2025 dramatic drop
  EMPHASIS_START: 2700,
  EMPHASIS_END: 3240,           // 90-108s: Emphasis beat with annotations
  CROSSING_START: 3240,
  CROSSING_END: 3600,           // 108-120s: Crossing point emphasis
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
  LINE_GENERATE: "#4A90D9",         // Blue - Cost to Generate
  LINE_PATCH: "#D9944A",            // Amber - Cost to Patch (Immediate)
  LINE_PATCH_TOTAL: "#D9944A",      // Amber - Total Cost (dashed)
  AREA_TECH_DEBT: "rgba(217, 148, 74, 0.3)", // Amber 30% opacity - Tech Debt
};

// Chart data points - FORKED DATA STRUCTURE
// At 2020, "Immediate Cost to Patch" forks into small and large codebase paths
export const CHART_DATA = {
  // Line 1 - Blue solid: Cost to Generate
  costToGenerate: [
    { year: 2015, hours: 32 },
    { year: 2020, hours: 30 },
    { year: 2022, hours: 28 },
    { year: 2023, hours: 15 },
    { year: 2024, hours: 6 },
    { year: 2025, hours: 3 },
  ],
  // Line 2 - Amber solid: Immediate Cost to Patch (pre-fork baseline, 2015-2020)
  immediateCostBaseline: [
    { year: 2015, hours: 10 },
    { year: 2020, hours: 10 },
  ],
  // Line 2a - Amber solid (bright): Small codebase fork (post-2020)
  immediateCostSmallCodebase: [
    { year: 2020, hours: 10 },
    { year: 2022, hours: 5 },
    { year: 2023, hours: 3 },
    { year: 2024, hours: 2 },
    { year: 2025, hours: 1.5 },
  ],
  // Line 2b - Amber solid (dimmer/thinner): Large codebase fork (post-2020)
  immediateCostLargeCodebase: [
    { year: 2020, hours: 10 },
    { year: 2022, hours: 10 },
    { year: 2023, hours: 11 },
    { year: 2024, hours: 12 },
    { year: 2025, hours: 12 },
  ],
  // Line 3 - Amber dashed: Total Cost of Patching, large codebase (= immediate + debt)
  // This line RISES from 25 to 33 — the key visual
  totalCostLargeCodebase: [
    { year: 2015, hours: 22 },
    { year: 2020, hours: 25 },
    { year: 2022, hours: 27 },
    { year: 2023, hours: 30 },
    { year: 2024, hours: 32 },
    { year: 2025, hours: 33 },
  ],
};

// Chart dimensions (within the canvas)
export const CHART_MARGINS = {
  top: 100,
  right: 300,
  bottom: 120,
  left: 180,
};

export const YEAR_RANGE = { min: 2015, max: 2025 };
export const HOURS_RANGE = { min: 0, max: 35 };

// Props schema
export const CodeCostChartProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultCodeCostChartProps: z.infer<typeof CodeCostChartProps> = {
  showTitle: true,
};

export type CodeCostChartPropsType = z.infer<typeof CodeCostChartProps>;

// Data point type
export interface DataPoint {
  year: number;
  hours: number;
}
