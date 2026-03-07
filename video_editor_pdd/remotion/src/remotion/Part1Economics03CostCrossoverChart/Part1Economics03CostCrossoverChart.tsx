import React from "react";
import {
  AbsoluteFill,
  Easing,
  interpolate,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
} from "remotion";
import { ChartAxes } from "./ChartAxes";
import { AnimatedLine } from "./AnimatedLine";
import { CrossoverPoint } from "./CrossoverPoint";
import {
  BG_COLOR,
  PATCHING_POINTS,
  GENERATION_POINTS,
  TOTAL_COST_POINTS,
  PATCHING_COLOR_START,
  PATCHING_COLOR_END,
  GENERATION_COLOR_START,
  GENERATION_COLOR_END,
  TOTAL_COST_COLOR,
  PRIMARY_LINE_WIDTH,
  TOTAL_LINE_WIDTH,
  LINE_A_START,
  LINE_A_END,
  LINE_B_START,
  LINE_B_END,
  LINE_C_START,
  LINE_C_END,
  CROSSOVER_DOT_START,
  CROSSOVER_LABEL_START,
  CROSSOVER_LABEL_END,
  CROSSOVER_PX_X,
  CROSSOVER_PX_Y,
  CENTER_X,
  CENTER_Y,
  ZOOM_START,
  ZOOM_END,
  ZOOM_SCALE_TARGET,
} from "./constants";

export const defaultPart1Economics03CostCrossoverChartProps = {};

export const Part1Economics03CostCrossoverChart: React.FC = () => {
  const frame = useCurrentFrame();

  // Act G zoom — scale toward crossover point, translating to center it on screen
  const zoomProgress = interpolate(
    frame,
    [ZOOM_START, ZOOM_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    },
  );

  const zoomScale = 1.0 + (ZOOM_SCALE_TARGET - 1.0) * zoomProgress;
  const translateX = (CENTER_X - CROSSOVER_PX_X) * zoomProgress;
  const translateY = (CENTER_Y - CROSSOVER_PX_Y) * zoomProgress;

  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part1_economics.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Chart overlay with Act G zoom transform */}
      <AbsoluteFill
        style={{
          transform: `translate(${translateX}px, ${translateY}px) scale(${zoomScale})`,
          transformOrigin: `${CROSSOVER_PX_X}px ${CROSSOVER_PX_Y}px`,
        }}
      >
        {/* Axes and grid — visible from frame 0 */}
        <ChartAxes />

        {/* Line A: Patching cost — draws frame 60-180 */}
        <AnimatedLine
          points={PATCHING_POINTS}
          gradientId="patchingGradient"
          colorStart={PATCHING_COLOR_START}
          colorEnd={PATCHING_COLOR_END}
          strokeWidth={PRIMARY_LINE_WIDTH}
          drawStartFrame={LINE_A_START}
          drawEndFrame={LINE_A_END}
          label="Cost of Patching"
          labelColor={PATCHING_COLOR_START}
        />

        {/* Line B: Generation cost — draws frame 120-240 */}
        <AnimatedLine
          points={GENERATION_POINTS}
          gradientId="generationGradient"
          colorStart={GENERATION_COLOR_START}
          colorEnd={GENERATION_COLOR_END}
          strokeWidth={PRIMARY_LINE_WIDTH}
          drawStartFrame={LINE_B_START}
          drawEndFrame={LINE_B_END}
          label="Cost of Generation"
          labelColor={GENERATION_COLOR_START}
        />

        {/* Line C: Total cost — fades frame 200-260 */}
        <AnimatedLine
          points={TOTAL_COST_POINTS}
          gradientId="totalCostGradient"
          colorStart={TOTAL_COST_COLOR}
          colorEnd={TOTAL_COST_COLOR}
          strokeWidth={TOTAL_LINE_WIDTH}
          drawStartFrame={LINE_C_START}
          drawEndFrame={LINE_C_END}
          dashed
          maxOpacity={0.6}
          label="Total Cost"
          labelColor={TOTAL_COST_COLOR}
        />

        {/* Crossover point + label */}
        <CrossoverPoint
          appearFrame={CROSSOVER_DOT_START}
          labelStartFrame={CROSSOVER_LABEL_START}
          labelEndFrame={CROSSOVER_LABEL_END}
        />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part1Economics03CostCrossoverChart;
