import { z } from "zod";

// Video specs
export const COMPOUND_CURVES_FPS = 30;
export const COMPOUND_CURVES_DURATION_SECONDS = 20;
export const COMPOUND_CURVES_DURATION_FRAMES =
  COMPOUND_CURVES_FPS * COMPOUND_CURVES_DURATION_SECONDS;
export const COMPOUND_CURVES_WIDTH = 1920;
export const COMPOUND_CURVES_HEIGHT = 1080;

// Color palette
export const COLORS = {
  BACKGROUND: "#1a1a2e",
  PATCHING_AMBER: "#D9944A",
  PDD_BLUE: "#4A90D9",
  PDD_GLOW: "#6AB0E9",
  DIP_RED: "#E06040",
  AXIS_WHITE: "rgba(255, 255, 255, 0.8)",
  LABEL_WHITE: "#ffffff",
  LABEL_DIM: "rgba(255, 255, 255, 0.7)",
  LEGEND_BORDER: "rgba(255, 255, 255, 0.2)",
  CEILING_DASH: "rgba(255, 255, 255, 0.4)",
  GAP_BLUE: "rgba(74, 144, 217, 0.15)",
  GAP_AMBER: "rgba(217, 148, 74, 0.10)",
};

// Graph layout constants (within the SVG viewBox)
export const GRAPH = {
  // Outer margins
  LEFT: 140,
  RIGHT: 1780,
  TOP: 100,
  BOTTOM: 900,
  // Derived
  get WIDTH() {
    return this.RIGHT - this.LEFT;
  },
  get HEIGHT() {
    return this.BOTTOM - this.TOP;
  },
  // Axis label positions
  X_LABEL_Y: 960,
  Y_LABEL_X: 50,
  // Legend box
  LEGEND_X: 200,
  LEGEND_Y: 130,
};

// Patching curve dots
export const PATCH_DOT_COUNT = 14;
export const PATCH_DOT_RADIUS = 8;

// PDD curve dots
export const PDD_DOT_COUNT = 14;
export const PDD_DOT_RADIUS = 8;

// Dip positions along the X-axis (as fraction 0-1)
export const DIP_POSITIONS = [0.55, 0.70, 0.85] as const;
export const DIP_LABELS = [
  "new bug from patch",
  "regression",
  "merge conflict",
] as const;
export const DIP_MAGNITUDES = [60, 45, 50] as const;
export const DIP_SPREAD = 0.04;

// Props schema
export const CompoundCurvesGraphProps = z.object({
  phase: z.number().min(1).max(5).default(1),
});

export const defaultCompoundCurvesGraphProps: z.infer<
  typeof CompoundCurvesGraphProps
> = {
  phase: 1,
};

export type CompoundCurvesGraphPropsType = z.infer<
  typeof CompoundCurvesGraphProps
>;
