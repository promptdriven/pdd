import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS, TIMING } from './constants';
import { ChartGrid } from './ChartGrid';
import { YAxis } from './YAxis';
import { XAxis } from './XAxis';
import { AnimatedBars } from './AnimatedBars';
import { ValueLabels } from './ValueLabels';

/**
 * AnimationSection02AnimatedBarChart
 *
 * An animated bar chart showing sample data comparison across four categories.
 * Bars animate in from bottom-to-top with smooth easing, followed by value labels.
 *
 * Duration: ~4s (120 frames at 30fps)
 */
export const AnimationSection02AnimatedBarChart: React.FC = () => {
  const centerX = 1920 / 2;
  const centerY = 1080 / 2;

  return (
    <AbsoluteFill style={{ backgroundColor: COLORS.background }}>
      <svg
        width={1920}
        height={1080}
        style={{
          position: 'absolute',
          top: 0,
          left: 0,
        }}
      >
        {/* Grid lines and axes */}
        <ChartGrid centerX={centerX} centerY={centerY} />
        <YAxis centerX={centerX} centerY={centerY} />
        <XAxis centerX={centerX} centerY={centerY} />

        {/* Animated bars */}
        <AnimatedBars centerX={centerX} centerY={centerY} />

        {/* Value labels */}
        <ValueLabels centerX={centerX} centerY={centerY} />
      </svg>
    </AbsoluteFill>
  );
};

export default AnimationSection02AnimatedBarChart;

export const defaultAnimationSection02AnimatedBarChartProps = {};
