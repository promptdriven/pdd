import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import {
  BG_COLOR,
  LABOR_COST_DATA,
  SOCK_COST_DATA,
  TOTAL_FRAMES,
  AMBER,
  BLUE,
} from './constants';
import { ChartAxes } from './ChartAxes';
import { AnimatedLine } from './AnimatedLine';
import { CrossingPointMarker } from './CrossingPoint';
import { ShadedArea } from './ShadedArea';

export const defaultPart1Economics02SockEconomicsChartProps = {};

export const Part1Economics02SockEconomicsChart: React.FC = () => {
  return (
    <AbsoluteFill
      style={{
        backgroundColor: BG_COLOR,
        width: 1920,
        height: 1080,
      }}
    >
      {/* Axes — draw from frame 0 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ChartAxes />
      </Sequence>

      {/* Animated lines — begin at frame 30 */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <AnimatedLine
          data={LABOR_COST_DATA}
          color={AMBER}
          strokeWidth={3}
          label="Cost to darn (time)"
        />
        <AnimatedLine
          data={SOCK_COST_DATA}
          color={BLUE}
          strokeWidth={3}
          label="Cost of new socks"
        />
      </Sequence>

      {/* Crossing point marker */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <CrossingPointMarker />
      </Sequence>

      {/* Shaded area + "Darning is irrational" label */}
      <Sequence from={0} durationInFrames={TOTAL_FRAMES}>
        <ShadedArea />
      </Sequence>
    </AbsoluteFill>
  );
};

export default Part1Economics02SockEconomicsChart;
