import { z } from "zod";

// Video specs from the animation doc
export const CROSSING_POINT_FPS = 30;
export const CROSSING_POINT_DURATION_SECONDS = 10;
export const CROSSING_POINT_DURATION_FRAMES = CROSSING_POINT_FPS * CROSSING_POINT_DURATION_SECONDS;
export const CROSSING_POINT_WIDTH = 1920;
export const CROSSING_POINT_HEIGHT = 1080;

// Beat timings (in frames at 30fps)
export const BEATS = {
  // Zoom out from milestone view
  ZOOM_OUT_START: 0,
  ZOOM_OUT_END: 60,              // 0-2s: Zoom out animation
  // Crossing point marker appears
  MARKER_APPEAR_START: 60,
  MARKER_APPEAR_END: 90,         // 2-3s: Radial burst appearance
  // First strong pulse
  PULSE_1_START: 90,
  PULSE_1_END: 150,              // 3-5s: First pulse wave
  // Label "We are here." fades in
  LABEL_FADE_START: 150,
  LABEL_FADE_END: 210,           // 5-7s: Label appears
  // Hold with continued pulsing
  HOLD_START: 210,
  HOLD_END: 300,                 // 7-10s: Hold with pulses
};

// Color palette
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
  MARKER: "#FFFFFF",                 // White circle
  MARKER_GLOW: "#4A90D9",           // Blue glow for the marker
  PULSE_GLOW: "#4A90D9",            // Blue pulse rings
};

// Data point type
export interface DataPoint {
  year: number;
  hours: number;
}

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
  ] as DataPoint[],
  // Line 2 - Amber solid: Immediate Cost to Patch (pre-fork baseline, 2015-2020)
  immediateCostBaseline: [
    { year: 2015, hours: 10 },
    { year: 2020, hours: 10 },
  ] as DataPoint[],
  // Line 2a - Amber solid (bright): Small codebase fork (post-2020)
  immediateCostSmallCodebase: [
    { year: 2020, hours: 10 },
    { year: 2022, hours: 5 },
    { year: 2023, hours: 3 },
    { year: 2024, hours: 2 },
    { year: 2025, hours: 1.5 },
  ] as DataPoint[],
  // Line 2b - Amber solid (dimmer/thinner): Large codebase fork (post-2020)
  immediateCostLargeCodebase: [
    { year: 2020, hours: 10 },
    { year: 2022, hours: 10 },
    { year: 2023, hours: 11 },
    { year: 2024, hours: 12 },
    { year: 2025, hours: 12 },
  ] as DataPoint[],
  // Line 3 - Amber dashed: Total Cost of Patching, large codebase (= immediate + debt)
  totalCostLargeCodebase: [
    { year: 2015, hours: 22 },
    { year: 2020, hours: 25 },
    { year: 2022, hours: 27 },
    { year: 2023, hours: 30 },
    { year: 2024, hours: 32 },
    { year: 2025, hours: 33 },
  ] as DataPoint[],
};

// Interpolate hours from a data series at a given year
export const interpolateHours = (data: DataPoint[], year: number): number => {
  if (year <= data[0].year) return data[0].hours;
  if (year >= data[data.length - 1].year) return data[data.length - 1].hours;

  for (let i = 0; i < data.length - 1; i++) {
    if (year >= data[i].year && year <= data[i + 1].year) {
      const t = (year - data[i].year) / (data[i + 1].year - data[i].year);
      return data[i].hours + t * (data[i + 1].hours - data[i].hours);
    }
  }
  return data[data.length - 1].hours;
};

// The crossing point (where generate crosses below large-codebase total cost)
// Between 2022-2023: generate goes 28→15, total goes 27→30
// 28 - 13t = 27 + 3t → t = 1/16 → year ≈ 2022.06, hours ≈ 27.19
export const CROSSING_POINT = {
  year: 2022.0625,
  hours: 27.1875,
};

// Chart margins
export const CHART_MARGINS = {
  top: 100,
  right: 250,
  bottom: 120,
  left: 180,
};

// Year range for code cost chart
export const YEAR_RANGE = { min: 2015, max: 2025 };
export const HOURS_RANGE = { min: 0, max: 35 };

// Pulse effect configuration - more dramatic than sock threshold
export const PULSE_CONFIG = {
  NUM_RINGS: 5,           // 4-5 concentric rings
  RING_STAGGER: 15,       // Frames between ring starts
  MAX_SCALE: 5,           // Rings expand more
  MARKER_RADIUS: 25,      // 25px radius as specified
};

// Props schema
export const CrossingPointProps = z.object({
  showTitle: z.boolean().default(true),
  showOverlayText: z.boolean().default(false),
  startAtFullView: z.boolean().default(false),
});

export const defaultCrossingPointProps: z.infer<typeof CrossingPointProps> = {
  showTitle: true,
  showOverlayText: false,
  startAtFullView: false,
};

export type CrossingPointPropsType = z.infer<typeof CrossingPointProps>;
