import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION } from './constants';

export const SparkleIcon: React.FC = () => {
  const frame = useCurrentFrame();

  // Sparkle rotates 360° during frames 15-20
  const rotation = interpolate(
    frame,
    [ANIMATION.sparkleRotateStart, ANIMATION.sparkleRotateEnd],
    [0, 360],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    },
  );

  return (
    <svg
      width={DIMENSIONS.sparkleSize}
      height={DIMENSIONS.sparkleSize}
      viewBox="0 0 16 16"
      fill="none"
      style={{
        marginRight: 8,
        flexShrink: 0,
        transform: `rotate(${rotation}deg)`,
      }}
    >
      {/* Four-point sparkle */}
      <path
        d="M8 0 C8.3 5 11 7.7 16 8 C11 8.3 8.3 11 8 16 C7.7 11 5 8.3 0 8 C5 7.7 7.7 5 8 0Z"
        fill={COLORS.sparkleIcon}
      />
    </svg>
  );
};
