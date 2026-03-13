import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION } from './constants';

export const CompletionRing: React.FC = () => {
  const frame = useCurrentFrame();

  const { circleRadius, circleStrokeWidth, circleCenterX, circleCenterY } =
    DIMENSIONS;
  const circumference = 2 * Math.PI * circleRadius;

  // Circle draws clockwise from top (frames 0-8) with easeInOutCubic
  const drawProgress = interpolate(
    frame,
    [ANIMATION.circleDrawStart, ANIMATION.circleDrawEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  const strokeDashoffset = circumference * (1 - drawProgress);

  // After frame 8, fill with subtle green tint
  const fillOpacity = interpolate(
    frame,
    [ANIMATION.checkDrawStart, ANIMATION.checkDrawEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const padding = circleStrokeWidth * 2;
  const svgSize = (circleRadius + padding) * 2;
  const center = svgSize / 2;

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
      <svg width={svgSize} height={svgSize} viewBox={`0 0 ${svgSize} ${svgSize}`}>
        <circle
          cx={center}
          cy={center}
          r={circleRadius}
          fill={`rgba(111,207,151,${0.1 * fillOpacity})`}
          stroke={COLORS.checkmark}
          strokeWidth={circleStrokeWidth}
          strokeDasharray={circumference}
          strokeDashoffset={strokeDashoffset}
          strokeLinecap="round"
          transform={`rotate(-90 ${center} ${center})`}
        />
      </svg>
    </div>
  );
};
