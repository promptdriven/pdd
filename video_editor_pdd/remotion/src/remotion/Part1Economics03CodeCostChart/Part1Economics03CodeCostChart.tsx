import React from "react";
import {
  AbsoluteFill,
  interpolate,
  useCurrentFrame,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  GENERATE_COST_DATA,
  IMMEDIATE_PATCH_DATA,
  TOTAL_COST_DEBT_DATA,
  GENERATE_LINE_COLOR,
  PATCH_LINE_COLOR,
  BLUE_LINE_START,
  BLUE_LINE_END,
  AMBER_SOLID_START,
  AMBER_SOLID_END,
  DASHED_LINE_START,
  DASHED_LINE_END,
  PULLBACK_START,
  PULLBACK_END,
} from "./constants";
import { ChartAxes } from "./ChartAxes";
import { AnimatedLine } from "./AnimatedLine";
import { DateMarkers } from "./DateMarkers";
import { DebtArea } from "./DebtArea";
import { PulseLine } from "./PulseLine";
import { Legend } from "./Legend";

export const defaultPart1Economics03CodeCostChartProps = {};

export const Part1Economics03CodeCostChart: React.FC = () => {
  const frame = useCurrentFrame();

  // Camera pullback: scale from 1.0 to 0.85 between PULLBACK_START and PULLBACK_END
  const scale = interpolate(
    frame,
    [PULLBACK_START, PULLBACK_END],
    [1.0, 0.85],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // During pullback, translate to keep chart centered
  const translateX = ((1 - scale) * CANVAS_WIDTH) / 2;
  const translateY = ((1 - scale) * CANVAS_HEIGHT) / 2;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      <div
        style={{
          width: CANVAS_WIDTH,
          height: CANVAS_HEIGHT,
          position: "absolute",
          top: 0,
          left: 0,
          transform: `translate(${translateX}px, ${translateY}px) scale(${scale})`,
          transformOrigin: "top left",
        }}
      >
        {/* Grid + Axes */}
        <ChartAxes />

        {/* Blue "Cost to generate" line */}
        <AnimatedLine
          data={GENERATE_COST_DATA}
          color={GENERATE_LINE_COLOR}
          strokeWidth={3}
          startFrame={BLUE_LINE_START}
          drawDuration={BLUE_LINE_END - BLUE_LINE_START}
          easing={Easing.inOut(Easing.cubic)}
        />

        {/* Date markers on blue line */}
        <DateMarkers />

        {/* Amber solid "Immediate patch cost" line */}
        <AnimatedLine
          data={IMMEDIATE_PATCH_DATA}
          color={PATCH_LINE_COLOR}
          strokeWidth={3}
          startFrame={AMBER_SOLID_START}
          drawDuration={AMBER_SOLID_END - AMBER_SOLID_START}
          easing={Easing.inOut(Easing.cubic)}
        />

        {/* Validation pulse on amber solid line */}
        <PulseLine />

        {/* Amber dashed "Total cost with debt" line */}
        <AnimatedLine
          data={TOTAL_COST_DEBT_DATA}
          color={PATCH_LINE_COLOR}
          strokeWidth={2.5}
          startFrame={DASHED_LINE_START}
          drawDuration={DASHED_LINE_END - DASHED_LINE_START}
          easing={Easing.out(Easing.quad)}
          dashArray="8 6"
        />

        {/* Shaded debt area between dashed and solid amber lines */}
        <DebtArea />

        {/* Legend */}
        <Legend />
      </div>
    </AbsoluteFill>
  );
};

export default Part1Economics03CodeCostChart;
