/**
 * ProgressRing component
 * Circular progress indicator that animates from 0° to 360°
 */

import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, POSITIONS, DIMENSIONS, ANIMATION } from './constants';

export const ProgressRing: React.FC = () => {
  const frame = useCurrentFrame();

  // Progress animation with easeInOutCubic
  const progress = interpolate(
    frame,
    [0, ANIMATION.COUNTER_DURATION],
    [0, 1],
    {
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const diameter = DIMENSIONS.PROGRESS_RING_DIAMETER;
  const strokeWidth = DIMENSIONS.PROGRESS_RING_STROKE;
  const radius = (diameter - strokeWidth) / 2;
  const circumference = 2 * Math.PI * radius;
  const offset = circumference * (1 - progress);

  return (
    <div
      style={{
        position: 'absolute',
        left: POSITIONS.COUNTER.X,
        top: POSITIONS.COUNTER.Y,
        transform: 'translate(-50%, -50%)',
      }}
    >
      <svg
        width={diameter}
        height={diameter}
        style={{
          transform: 'rotate(-90deg)',
        }}
      >
        {/* Background circle */}
        <circle
          cx={diameter / 2}
          cy={diameter / 2}
          r={radius}
          fill="none"
          stroke={COLORS.PROGRESS_RING}
          strokeWidth={strokeWidth}
          opacity={0.15}
        />
        {/* Animated progress circle */}
        <circle
          cx={diameter / 2}
          cy={diameter / 2}
          r={radius}
          fill="none"
          stroke={COLORS.PROGRESS_RING}
          strokeWidth={strokeWidth}
          strokeDasharray={circumference}
          strokeDashoffset={offset}
          strokeLinecap="round"
          opacity={0.8}
        />
      </svg>
    </div>
  );
};
