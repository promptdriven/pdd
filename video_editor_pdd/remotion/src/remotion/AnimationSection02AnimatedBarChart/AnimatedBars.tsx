import React from 'react';
import { Easing, interpolate, useCurrentFrame } from 'remotion';
import { DIMENSIONS, CHART_DATA, TIMING, STAGGER_DELAY, MAX_VALUE } from './constants';

interface AnimatedBarsProps {
  centerX: number;
  centerY: number;
}

export const AnimatedBars: React.FC<AnimatedBarsProps> = ({ centerX, centerY }) => {
  const frame = useCurrentFrame();

  const chartLeft = centerX - DIMENSIONS.chartWidth / 2;
  const chartBottom = centerY + DIMENSIONS.chartHeight / 2;

  const totalBarsWidth = CHART_DATA.length * DIMENSIONS.barWidth + (CHART_DATA.length - 1) * DIMENSIONS.barGap;
  const startX = chartLeft + (DIMENSIONS.chartWidth - totalBarsWidth) / 2;

  return (
    <>
      {CHART_DATA.map((item, index) => {
        const barX = startX + index * (DIMENSIONS.barWidth + DIMENSIONS.barGap);
        const maxHeight = (item.value / MAX_VALUE) * DIMENSIONS.chartHeight;

        const animationStart = TIMING.barsStart + index * STAGGER_DELAY;
        const animationEnd = animationStart + TIMING.barsDuration;

        const currentHeight = interpolate(
          frame,
          [animationStart, animationEnd],
          [0, maxHeight],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.cubic),
          }
        );

        return (
          <rect
            key={item.category}
            x={barX}
            y={chartBottom - currentHeight}
            width={DIMENSIONS.barWidth}
            height={currentHeight}
            fill={item.color}
            rx={DIMENSIONS.borderRadius}
            ry={DIMENSIONS.borderRadius}
          />
        );
      })}
    </>
  );
};
