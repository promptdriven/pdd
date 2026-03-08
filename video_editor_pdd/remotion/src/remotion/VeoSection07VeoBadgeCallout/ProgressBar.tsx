import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, POSITIONS, DIMENSIONS, ANIMATION, CANVAS } from './constants';

export const ProgressBar: React.FC = () => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [ANIMATION.progressStart, ANIMATION.progressStart + ANIMATION.progressDuration],
    [0, 100],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  if (frame < ANIMATION.progressStart) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: POSITIONS.progressBarY,
        width: CANVAS.width,
        height: DIMENSIONS.progressBarHeight,
        backgroundColor: COLORS.progressBarTrack,
        borderRadius: DIMENSIONS.progressBarBorderRadius,
      }}
    >
      <div
        style={{
          width: `${progress}%`,
          height: '100%',
          backgroundColor: COLORS.progressBar,
          borderRadius: DIMENSIONS.progressBarBorderRadius,
          boxShadow: `0 0 8px ${COLORS.progressBar}60`,
        }}
      />
    </div>
  );
};
