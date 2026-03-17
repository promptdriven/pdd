import React from "react";
import { AbsoluteFill, Sequence } from "remotion";
import { ChartAxes } from "./ChartAxes";
import { AnimatedLine } from "./AnimatedLine";
import { CrossingPointMarker } from "./CrossingPoint";
import { ShadedArea } from "./ShadedArea";
import {
  BG_COLOR,
  TOTAL_FRAMES,
  AMBER,
  BLUE,
  LABOR_COST_DATA,
  SOCK_COST_DATA,
} from "./constants";

export const defaultPart1Economics02SockEconomicsChartProps = {};

/**
 * Sock Economics Chart — Labor Cost vs Garment Cost
 *
 * Animated dual-line crossover chart showing the moment when buying new socks
 * became cheaper than darning. Y-axis: cost as % of hourly wage. X-axis: 1950–1975.
 * Amber line (labor cost to darn) stays flat ~33%. Blue line (new sock cost) drops
 * from 80% to 14%. They cross at ~1962 — "The Threshold."
 *
 * 540 frames (18s at 30fps).
 */
export const Part1Economics02SockEconomicsChart: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: BG_COLOR }}>
      {/* Axes and grid */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ChartAxes />
      </Sequence>

      {/* Labor cost line (amber, roughly flat) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <AnimatedLine
          data={LABOR_COST_DATA}
          color={AMBER}
          label="Cost to darn (time)"
        />
      </Sequence>

      {/* New sock cost line (blue, declining) */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <AnimatedLine
          data={SOCK_COST_DATA}
          color={BLUE}
          label="Cost of new socks"
        />
      </Sequence>

      {/* Shaded area between lines after crossing */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ShadedArea />
      </Sequence>

      {/* Crossing point marker + "The Threshold" label */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <CrossingPointMarker />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics02SockEconomicsChart;
