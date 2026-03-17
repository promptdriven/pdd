import React from "react";
import { AbsoluteFill, useCurrentFrame } from "remotion";
import { ChartAxes } from "./ChartAxes";
import { AnimatedLine } from "./AnimatedLine";
import { DebtArea } from "./DebtArea";
import {
  BG_COLOR,
  BLUE_LINE_COLOR,
  AMBER_LINE_COLOR,
  BLUE_STROKE_WIDTH,
  AMBER_SOLID_STROKE_WIDTH,
  AMBER_DASHED_STROKE_WIDTH,
  BLUE_LINE_START,
  BLUE_LINE_END,
  AMBER_SOLID_START,
  AMBER_SOLID_END,
  AMBER_DASHED_START,
  AMBER_DASHED_END,
  GENERATE_COST_DATA,
  PATCH_COST_DATA,
  TOTAL_COST_DATA,
} from "./constants";
import "../_shared/load-inter-font";

export const defaultPart1Economics03CodeCostTripleLineProps = {};

export const Part1Economics03CodeCostTripleLine: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Axes, grid, tick labels, and AI milestone markers */}
      <ChartAxes />

      {/* Line 1: Cost to generate (blue, solid) — draws frame 60-180 */}
      <AnimatedLine
        data={GENERATE_COST_DATA}
        color={BLUE_LINE_COLOR}
        strokeWidth={BLUE_STROKE_WIDTH}
        drawStartFrame={BLUE_LINE_START}
        drawEndFrame={BLUE_LINE_END}
        label="Cost to generate"
        labelOpacityMultiplier={0.7}
      />

      {/* Line 2: Immediate patch cost (amber, solid) — draws frame 180-300 */}
      <AnimatedLine
        data={PATCH_COST_DATA}
        color={AMBER_LINE_COLOR}
        strokeWidth={AMBER_SOLID_STROKE_WIDTH}
        drawStartFrame={AMBER_SOLID_START}
        drawEndFrame={AMBER_SOLID_END}
        label="Immediate patch cost"
        labelOpacityMultiplier={0.7}
      />

      {/* Line 3: Total cost with debt (amber, dashed) — draws frame 300-420 */}
      <AnimatedLine
        data={TOTAL_COST_DATA}
        color={AMBER_LINE_COLOR}
        strokeWidth={AMBER_DASHED_STROKE_WIDTH}
        drawStartFrame={AMBER_DASHED_START}
        drawEndFrame={AMBER_DASHED_END}
        dashed
        dashArray="8 4"
        label="Total cost (with debt)"
        labelOpacityMultiplier={0.5}
      />

      {/* Debt shaded area between solid and dashed amber lines — fills frame 420-540, then pulses */}
      <DebtArea />
    </AbsoluteFill>
  );
};

export default Part1Economics03CodeCostTripleLine;
