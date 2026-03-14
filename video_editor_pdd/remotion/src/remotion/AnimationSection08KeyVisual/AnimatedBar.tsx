import React from 'react';
import { interpolate, useCurrentFrame } from 'remotion';
import { DIMENSIONS, TIMING, COLORS } from './constants';

interface AnimatedBarProps {
  targetHeight: number;
  delay: number;
  color: string;
}

export const AnimatedBar: React.FC<AnimatedBarProps> = ({
  targetHeight,
  delay,
  color,
}) => {
  const frame = useCurrentFrame();

  const currentHeight = interpolate(
    frame,
    [delay, delay + TIMING.barGrowDuration],
    [0, targetHeight],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  return (
    <div
      style={{
        width: DIMENSIONS.barWidth,
        height: currentHeight,
        backgroundColor: color,
        borderRadius: DIMENSIONS.barRadius,
        boxShadow: `0 12px 40px ${COLORS.barShadow}`,
      }}
    />
  );
};
