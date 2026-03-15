import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { DIMENSIONS, TIMING, COLORS } from './constants';

interface AnimatedBarProps {
  targetHeight: number;
  delay: number;
  color: string;
  isTallest: boolean;
}

export const AnimatedBar: React.FC<AnimatedBarProps> = ({
  targetHeight,
  delay,
  color,
  isTallest,
}) => {
  const frame = useCurrentFrame();

  const growEnd = delay + TIMING.barGrowFrames;

  const currentHeight = interpolate(
    frame,
    [delay, growEnd],
    [0, targetHeight],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.4)),
    },
  );

  // Pulse glow on tallest bar after all bars finish growing
  const pulseOpacity = isTallest
    ? interpolate(
        frame,
        [TIMING.pulseStart, TIMING.pulseStart + 3, TIMING.totalFrames],
        [0, 0.6, 0.3],
        { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
      )
    : 0;

  return (
    <div
      style={{
        width: DIMENSIONS.barWidth,
        height: Math.max(0, currentHeight),
        backgroundColor: color,
        borderRadius: DIMENSIONS.barBorderRadius,
        boxShadow: `0 4px 12px ${COLORS.barShadow}${
          pulseOpacity > 0
            ? `, 0 0 24px rgba(34, 197, 94, ${pulseOpacity})`
            : ''
        }`,
        flexShrink: 0,
      }}
    />
  );
};
