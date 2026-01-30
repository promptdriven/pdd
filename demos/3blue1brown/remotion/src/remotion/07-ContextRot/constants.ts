import { z } from "zod";

// Video specs for Context Rot section
export const CONTEXT_ROT_FPS = 30;
export const CONTEXT_ROT_DURATION_SECONDS = 45;
export const CONTEXT_ROT_DURATION_FRAMES = CONTEXT_ROT_FPS * CONTEXT_ROT_DURATION_SECONDS; // 1350 frames
export const CONTEXT_ROT_WIDTH = 1920;
export const CONTEXT_ROT_HEIGHT = 1080;

// Animation beat timings (in frames at 30fps)
export const BEATS = {
  // Part 1: Zoom Into the Debt (0-10s, frames 0-300)
  ZOOM_INTO_DEBT_START: 0,
  ZOOM_INTO_DEBT_END: 60,
  LAYER_SEPARATION_START: 60,
  LAYER_SEPARATION_END: 150,
  HOLD_LAYERS_START: 150,
  HOLD_LAYERS_END: 300,

  // Part 2: The Shrinking Window (10-30s, frames 300-900)
  MORPH_TO_GRID_START: 300,
  MORPH_TO_GRID_END: 360,
  SMALL_CODEBASE_START: 360,
  SMALL_CODEBASE_END: 540,
  CODEBASE_GROWTH_START: 540,
  CODEBASE_GROWTH_END: 720,
  LARGE_CODEBASE_START: 720,
  LARGE_CODEBASE_END: 900,

  // Part 3: The Consequence (30-45s, frames 900-1350)
  SPLIT_VIEW_START: 900,
  SPLIT_VIEW_END: 1020,
  RETURN_TO_CHART_START: 1020,
  RETURN_TO_CHART_END: 1140,
  SETUP_SOLUTION_START: 1140,
  SETUP_SOLUTION_END: 1350,
};

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  BACKGROUND_GRADIENT_END: "#0f0f1a",
  GRID: "#333344",
  AXIS: "#666677",
  AXIS_LABEL: "rgba(255, 255, 255, 0.8)",
  TITLE: "#ffffff",

  // Debt layers
  CODE_COMPLEXITY: "#D9944A", // Darker amber for code complexity
  CONTEXT_ROT: "#E8B888",     // Lighter amber for context rot

  // Context window visualization
  CONTEXT_WINDOW_BORDER: "#4A90D9", // Glowing blue

  // Code blocks
  RELEVANT_CODE: "#5AAA6E",   // Soft green glow
  IRRELEVANT_CODE: "#944A4A", // Red tint

  // Chart lines (from previous sections)
  LINE_GENERATE: "#4A90D9",
  LINE_PATCH: "#D9944A",

  // Code block base colors
  CODE_BLOCK_COLORS: [
    "#3D3D5C",
    "#4A4A6E",
    "#555580",
    "#404060",
    "#484878",
  ],
};

// Grid configuration
export const GRID_CONFIG = {
  SMALL_SIZE: 4,    // 4x4 grid
  MEDIUM_SIZE: 8,   // 8x8 grid
  LARGE_SIZE: 16,   // 16x16 grid
  XLARGE_SIZE: 32,  // 32x32 grid
  BLOCK_GAP: 4,
  BLOCK_RADIUS: 4,
};

// Context coverage percentages at each grid size
export const CONTEXT_COVERAGE = {
  SMALL: 80,   // 4x4 grid - 80% coverage
  MEDIUM: 40,  // 8x8 grid - 40% coverage
  LARGE: 10,   // 16x16 grid - 10% coverage
  XLARGE: 2,   // 32x32 grid - 2% coverage
};

// Chart margins (reusing from previous sections)
export const CHART_MARGINS = {
  top: 100,
  right: 250,
  bottom: 120,
  left: 180,
};

// Year range (matching CodeCostChart)
export const YEAR_RANGE = { min: 2015, max: 2025 };
export const HOURS_RANGE = { min: 0, max: 35 };

// Data point type
export interface DataPoint {
  year: number;
  hours: number;
}

// Interpolate data to get hours at any year
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

// Chart data from CodeCostChart (forked structure)
export const CHART_DATA = {
  costToGenerate: [
    { year: 2015, hours: 32 },
    { year: 2020, hours: 30 },
    { year: 2022, hours: 28 },
    { year: 2023, hours: 15 },
    { year: 2024, hours: 6 },
    { year: 2025, hours: 3 },
  ] as DataPoint[],
  immediateCostBaseline: [
    { year: 2015, hours: 10 },
    { year: 2020, hours: 10 },
  ] as DataPoint[],
  immediateCostSmallCodebase: [
    { year: 2020, hours: 10 },
    { year: 2022, hours: 5 },
    { year: 2023, hours: 3 },
    { year: 2024, hours: 2 },
    { year: 2025, hours: 1.5 },
  ] as DataPoint[],
  immediateCostLargeCodebase: [
    { year: 2020, hours: 10 },
    { year: 2022, hours: 10 },
    { year: 2023, hours: 11 },
    { year: 2024, hours: 12 },
    { year: 2025, hours: 12 },
  ] as DataPoint[],
  totalCostLargeCodebase: [
    { year: 2015, hours: 22 },
    { year: 2020, hours: 25 },
    { year: 2022, hours: 27 },
    { year: 2023, hours: 30 },
    { year: 2024, hours: 32 },
    { year: 2025, hours: 33 },
  ] as DataPoint[],
};

// Spring animation config
export const SPRING_CONFIG = {
  damping: 12,
  stiffness: 200,
};

// Props schema
export const ContextRotProps = z.object({
  showTitle: z.boolean().default(true),
});

export const defaultContextRotProps: z.infer<typeof ContextRotProps> = {
  showTitle: true,
};

export type ContextRotPropsType = z.infer<typeof ContextRotProps>;
