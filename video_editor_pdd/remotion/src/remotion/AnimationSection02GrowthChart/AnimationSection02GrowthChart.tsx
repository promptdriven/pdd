import React from 'react';
import { AbsoluteFill, Sequence } from 'remotion';
import { CHART_CONFIG, ANIMATION_TIMING } from './constants';
import { GridLines } from './GridLines';
import { AxisLines } from './AxisLines';
import { AxisLabels } from './AxisLabels';
import { AnimatedLine } from './AnimatedLine';
import { DataPoints } from './DataPoints';
import { ChartTitle } from './ChartTitle';
import { FinalPulse } from './FinalPulse';

export const AnimationSection02GrowthChart: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: CHART_CONFIG.background }}>
      <Sequence from={0} durationInFrames={ANIMATION_TIMING.totalDuration}>
        <FinalPulse>
          {/* Grid lines - fade in sequentially */}
          <Sequence from={ANIMATION_TIMING.gridFadeIn.start}>
            <GridLines />
          </Sequence>

          {/* Axis lines - draw from origin */}
          <Sequence from={ANIMATION_TIMING.axisDrawIn.start}>
            <AxisLines />
          </Sequence>

          {/* Chart title and axis labels - fade in with scale */}
          <Sequence from={ANIMATION_TIMING.labelsFadeIn.start}>
            <ChartTitle />
            <AxisLabels />
          </Sequence>

          {/* Data line with area fill */}
          <Sequence from={ANIMATION_TIMING.lineDrawIn.start}>
            <AnimatedLine />
          </Sequence>

          {/* Data points with staggered pulse */}
          <Sequence from={ANIMATION_TIMING.pointsAppear.start}>
            <DataPoints />
          </Sequence>
        </FinalPulse>
      </Sequence>
    </AbsoluteFill>
  );
};

export const defaultAnimationSection02GrowthChartProps = {};

export default AnimationSection02GrowthChart;
