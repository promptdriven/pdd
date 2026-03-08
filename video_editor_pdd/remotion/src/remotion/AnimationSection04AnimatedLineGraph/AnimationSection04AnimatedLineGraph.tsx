import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS, TIMING, DATA } from './constants';
import { GraphGrid } from './GraphGrid';
import { Axes } from './Axes';
import { Legend } from './Legend';
import { AnimatedLineSeries } from './AnimatedLineSeries';

export const defaultAnimationSection04AnimatedLineGraphProps = {};

export const AnimationSection04AnimatedLineGraph: React.FC = () => {
  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      {/* Grid and axes - fade in from frame 0-15 */}
      <GraphGrid
        verticalLines={7}
        horizontalLines={5}
        fadeInDuration={TIMING.gridFadeIn.duration}
      />
      <Axes fadeInDuration={TIMING.gridFadeIn.duration} />

      {/* Legend - fade in from frame 15-20 */}
      <Legend
        startFrame={TIMING.legendFadeIn.start}
        fadeInDuration={TIMING.legendFadeIn.duration}
      />

      {/* Series 1 - Target (blue) - draws from frame 20-80 */}
      <AnimatedLineSeries
        data={DATA.series1}
        color={COLORS.series1}
        strokeWidth={3}
        glowRadius={12}
        startFrame={TIMING.series1Draw.start}
        duration={TIMING.series1Draw.duration}
      />

      {/* Series 2 - Actual (violet) - draws from frame 40-100 */}
      <AnimatedLineSeries
        data={DATA.series2}
        color={COLORS.series2}
        strokeWidth={3}
        glowRadius={12}
        startFrame={TIMING.series2Draw.start}
        duration={TIMING.series2Draw.duration}
      />
    </AbsoluteFill>
  );
};

export default AnimationSection04AnimatedLineGraph;
