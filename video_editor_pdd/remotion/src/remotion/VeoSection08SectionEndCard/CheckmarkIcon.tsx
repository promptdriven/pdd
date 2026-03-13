import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLORS,
  DIMENSIONS,
  ANIMATION,
  CHECK_PATH,
  CHECK_PATH_LENGTH,
} from './constants';

export const CheckmarkIcon: React.FC = () => {
  const frame = useCurrentFrame();

  const { circleCenterX, circleCenterY, circleRadius, checkStrokeWidth } =
    DIMENSIONS;

  // Check stroke draws in (frames 8-16) with easeOutQuad
  const drawProgress = interpolate(
    frame,
    [ANIMATION.checkDrawStart, ANIMATION.checkDrawEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const dashOffset = CHECK_PATH_LENGTH * (1 - drawProgress);

  // SVG viewBox is 120x120 (matching the circle diameter area)
  // The check path is drawn in a 120x120 coordinate space
  const svgSize = circleRadius * 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: circleCenterX - svgSize / 2,
        top: circleCenterY - svgSize / 2,
        width: svgSize,
        height: svgSize,
      }}
    >
      <svg
        width={svgSize}
        height={svgSize}
        viewBox="0 0 120 120"
        fill="none"
      >
        <path
          d={CHECK_PATH}
          stroke={COLORS.checkmark}
          strokeWidth={checkStrokeWidth}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={CHECK_PATH_LENGTH}
          strokeDashoffset={dashOffset}
        />
      </svg>
    </div>
  );
};
