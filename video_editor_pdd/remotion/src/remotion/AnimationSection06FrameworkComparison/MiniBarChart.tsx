import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, BAR_DATA, ANIMATION_TIMING } from './constants';

export const MiniBarChart: React.FC = () => {
  const frame = useCurrentFrame();

  const bars = BAR_DATA.heights;
  const totalBarWidth =
    bars.length * DIMENSIONS.barWidth + (bars.length - 1) * DIMENSIONS.barGap;
  const startX = -totalBarWidth / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: 240,
        bottom: 200,
        width: totalBarWidth,
        height: BAR_DATA.maxBarHeight,
        transform: 'translateX(-50%)',
      }}
    >
      {bars.map((heightFraction, i) => {
        const barStart = ANIMATION_TIMING.barGrowStart + i * ANIMATION_TIMING.barStagger;
        const barEnd = barStart + ANIMATION_TIMING.barGrowDuration;
        const targetHeight = heightFraction * BAR_DATA.maxBarHeight;

        const barHeight = interpolate(
          frame,
          [barStart, barEnd],
          [0, targetHeight],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: i * (DIMENSIONS.barWidth + DIMENSIONS.barGap),
              bottom: 0,
              width: DIMENSIONS.barWidth,
              height: barHeight,
              backgroundColor: COLORS.barColors[i % COLORS.barColors.length],
              borderRadius: 4,
            }}
          />
        );
      })}
    </div>
  );
};
