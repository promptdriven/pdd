import React from "react";
import {
  AbsoluteFill,
  Sequence,
  OffthreadVideo,
  staticFile,
  useCurrentFrame,
  interpolate,
  Easing,
} from "remotion";
import { ChartAxes } from "./ChartAxes";
import { AnimatedLine } from "./AnimatedLine";
import { CrossoverPoint } from "./CrossoverPoint";

// Data points (normalized 0-1)
const PATCHING_POINTS = [
  { x: 0, y: 0.15 },
  { x: 0.2, y: 0.22 },
  { x: 0.4, y: 0.35 },
  { x: 0.6, y: 0.55 },
  { x: 0.8, y: 0.78 },
  { x: 1.0, y: 0.95 },
];

const GENERATION_POINTS = [
  { x: 0, y: 0.9 },
  { x: 0.2, y: 0.72 },
  { x: 0.4, y: 0.5 },
  { x: 0.6, y: 0.35 },
  { x: 0.8, y: 0.25 },
  { x: 1.0, y: 0.18 },
];

const TOTAL_COST_POINTS = [
  { x: 0, y: 0.82 },
  { x: 0.2, y: 0.83 },
  { x: 0.4, y: 0.84 },
  { x: 0.6, y: 0.86 },
  { x: 0.8, y: 0.87 },
  { x: 1.0, y: 0.88 },
];

// Crossover pixel position for zoom target
const CHART_X = 200;
const CHART_Y = 100;
const CHART_W = 1620;
const CHART_H = 780;
const CROSSOVER = { x: 0.42, y: 0.48 };
const CROSSOVER_PX_X = CHART_X + CROSSOVER.x * CHART_W;
const CROSSOVER_PX_Y = CHART_Y + CHART_H * (1 - CROSSOVER.y);

// Act G zoom timing (around frame 11100 from global, but relative to this component)
const ZOOM_START = 2600;
const ZOOM_END = 2700;

export const defaultPart1Economics03CostCrossoverChartProps = {};

export const Part1Economics03CostCrossoverChart: React.FC = () => {
  const frame = useCurrentFrame();

  // Act G zoom effect — zooms to crossover point
  const zoomScale = interpolate(
    frame,
    [ZOOM_START, ZOOM_END],
    [1.0, 2.5],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Translate to keep crossover point centered during zoom
  const translateX = interpolate(
    frame,
    [ZOOM_START, ZOOM_END],
    [0, -(CROSSOVER_PX_X - 960) * (zoomScale - 1)],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const translateY = interpolate(
    frame,
    [ZOOM_START, ZOOM_END],
    [0, -(CROSSOVER_PX_Y - 540) * (zoomScale - 1)],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  return (
    <AbsoluteFill style={{ backgroundColor: "#0A1628" }}>
      {/* Veo background video */}
      <AbsoluteFill>
        <OffthreadVideo
          src={staticFile("veo/part1_economics.mp4")}
          style={{ width: "100%", height: "100%", objectFit: "cover" }}
          muted
        />
      </AbsoluteFill>

      {/* Chart overlay with zoom transform */}
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
          colorStart="#EF4444"
          colorEnd="#F59E0B"
          strokeWidth={4}
          drawStartFrame={60}
          drawEndFrame={180}
          label="Cost of Patching"
          labelColor="#EF4444"
        />

        {/* Line B: Generation cost — draws frame 120-240 */}
        <AnimatedLine
          points={GENERATION_POINTS}
          gradientId="generationGradient"
          colorStart="#3B82F6"
          colorEnd="#22C55E"
          strokeWidth={4}
          drawStartFrame={120}
          drawEndFrame={240}
          label="Cost of Generation"
          labelColor="#3B82F6"
        />

        {/* Line C: Total cost — fades frame 200-260 */}
        <AnimatedLine
          points={TOTAL_COST_POINTS}
          gradientId="totalCostGradient"
          colorStart="#94A3B8"
          colorEnd="#94A3B8"
          strokeWidth={2}
          drawStartFrame={200}
          drawEndFrame={260}
          dashed
          maxOpacity={0.6}
          label="Total Cost"
          labelColor="#94A3B8"
        />

        {/* Crossover point + label */}
        <CrossoverPoint
          appearFrame={250}
          labelStartFrame={280}
          labelEndFrame={310}
        />
      </AbsoluteFill>
    </AbsoluteFill>
  );
};

export default Part1Economics03CostCrossoverChart;
