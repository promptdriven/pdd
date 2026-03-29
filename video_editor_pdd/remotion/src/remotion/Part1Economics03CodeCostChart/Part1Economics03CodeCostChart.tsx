import React from "react";
import {
  AbsoluteFill,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import {
  BG_COLOR,
  BLUE_LINE_COLOR,
  AMBER_LINE_COLOR,
  GENERATE_COST_DATA,
  IMMEDIATE_PATCH_DATA,
  TOTAL_COST_DEBT_DATA,
  BLUE_LINE_START,
  BLUE_LINE_END,
  AMBER_SOLID_START,
  AMBER_SOLID_END,
  PULSE_START,
  PULSE_END,
  DASHED_START,
  DASHED_END,
  PULLBACK_START,
  PULLBACK_END,
  PULLBACK_SCALE_FROM,
  PULLBACK_SCALE_TO,
} from "./constants";
import { ChartAxes } from "./ChartAxes";
import { AnimatedLine } from "./AnimatedLine";
import { DateMarkersOverlay } from "./DateMarkers";
import { ShadedDebtArea } from "./ShadedDebtArea";
import { ChartLegend } from "./Legend";

export const defaultPart1Economics03CodeCostChartProps = {};

export const Part1Economics03CodeCostChart: React.FC = () => {
  const frame = useCurrentFrame();

  // Camera pullback scale
  const scale = interpolate(
    frame,
    [PULLBACK_START, PULLBACK_END],
    [PULLBACK_SCALE_FROM, PULLBACK_SCALE_TO],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        overflow: "hidden",
      }}
    >
      {/* Scaled chart container for camera pullback */}
      <AbsoluteFill
        style={{
          transform: `scale(${scale})`,
          transformOrigin: "center center",
        }}
      >
        {/* Phase 1: Axes draw from frame 0 */}
        <ChartAxes />

        {/* Phase 2-3: Blue "Cost to generate" line (frames 45-300) */}
        <AnimatedLine
          data={GENERATE_COST_DATA}
          color={BLUE_LINE_COLOR}
          strokeWidth={3}
          startFrame={BLUE_LINE_START}
          drawDuration={BLUE_LINE_END - BLUE_LINE_START}
          easing={Easing.inOut(Easing.cubic)}
        />

        {/* Date markers appear as blue line passes each year */}
        <DateMarkersOverlay />

        {/* Phase 4: Amber solid "Immediate patch cost" (frames 300-450) */}
        <AnimatedLine
          data={IMMEDIATE_PATCH_DATA}
          color={AMBER_LINE_COLOR}
          strokeWidth={3}
          startFrame={AMBER_SOLID_START}
          drawDuration={AMBER_SOLID_END - AMBER_SOLID_START}
          glowActive
          glowStartFrame={PULSE_START}
          glowEndFrame={PULSE_END}
          easing={Easing.inOut(Easing.cubic)}
        />

        {/* Phase 5-6: Amber dashed "Total cost with debt" (frames 540-600) */}
        <AnimatedLine
          data={TOTAL_COST_DEBT_DATA}
          color={AMBER_LINE_COLOR}
          strokeWidth={2.5}
          startFrame={DASHED_START}
          drawDuration={DASHED_END - DASHED_START}
          dashArray="8 6"
          easing={Easing.out(Easing.quad)}
        />

        {/* Shaded debt area between amber lines */}
        <ShadedDebtArea />

        {/* Legend */}
        <ChartLegend />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part1Economics03CodeCostChart;
