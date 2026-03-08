import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, POSITIONS, ANIMATION_TIMING, CANVAS } from './constants';

export const AnimatedCheckmark: React.FC = () => {
  const frame = useCurrentFrame();

  // Circle circumference: 2 * PI * radius
  const circumference = 2 * Math.PI * DIMENSIONS.checkmarkRadius;

  // Circle draws from frame 5 to 15
  const circleProgress = interpolate(
    frame,
    [ANIMATION_TIMING.checkmarkStart, ANIMATION_TIMING.checkmarkStart + 10],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const circleDashOffset = circumference * (1 - circleProgress);

  // Checkmark path draws from frame 15 to 25
  // Approximate checkmark path length
  const checkmarkPathLength = 50;
  const checkmarkProgress = interpolate(
    frame,
    [ANIMATION_TIMING.checkmarkStart + 10, ANIMATION_TIMING.checkmarkEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const checkmarkDashOffset = checkmarkPathLength * (1 - checkmarkProgress);

  // SVG viewBox size (64px diameter + padding)
  const svgSize = 80;
  const cx = svgSize / 2;
  const cy = svgSize / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.width / 2 - svgSize / 2,
        top: POSITIONS.checkmarkCy - svgSize / 2,
        width: svgSize,
        height: svgSize,
      }}
    >
      <svg
        width={svgSize}
        height={svgSize}
        viewBox={`0 0 ${svgSize} ${svgSize}`}
      >
        {/* Circle */}
        <circle
          cx={cx}
          cy={cy}
          r={DIMENSIONS.checkmarkRadius}
          fill="none"
          stroke={COLORS.checkmark}
          strokeWidth={DIMENSIONS.checkmarkStrokeWidth}
          strokeDasharray={circumference}
          strokeDashoffset={circleDashOffset}
          strokeLinecap="round"
          transform={`rotate(-90, ${cx}, ${cy})`}
        />
        {/* Checkmark path */}
        <path
          d={`M ${cx - 12} ${cy + 1} L ${cx - 3} ${cy + 10} L ${cx + 14} ${cy - 10}`}
          fill="none"
          stroke={COLORS.checkmark}
          strokeWidth={DIMENSIONS.checkmarkStrokeWidth}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={checkmarkPathLength}
          strokeDashoffset={checkmarkDashOffset}
        />
      </svg>
    </div>
  );
};
