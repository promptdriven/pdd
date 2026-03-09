import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const ProgressBar: React.FC = () => {
  const frame = useCurrentFrame();

  // Progress bar fills from 0% to 100% (frame 15-75), linear easing
  const progress = interpolate(
    frame,
    [ANIMATION_TIMING.progressStart, ANIMATION_TIMING.progressEnd],
    [0, 100],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        bottom: 0,
        left: 0,
        width: '100%',
        height: DIMENSIONS.progressBarHeight,
      }}
    >
      <div
        style={{
          width: `${progress}%`,
          height: '100%',
          backgroundColor: COLORS.progress,
          borderRadius: `0 0 0 ${DIMENSIONS.pillBorderRadius}px`,
        }}
      />
    </div>
  );
};
