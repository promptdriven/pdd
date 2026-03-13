import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, DIMENSIONS, ANIMATION_TIMING, CHECKMARK_PATH, CHECKMARK_PATH_LENGTH } from './constants';

export const DrawCheckmark: React.FC = () => {
  const frame = useCurrentFrame();

  // Stroke draws in over frames 0-9 with easeInOutCubic
  const drawProgress = interpolate(
    frame,
    [ANIMATION_TIMING.checkmarkDrawStart, ANIMATION_TIMING.checkmarkDrawEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const dashOffset = CHECKMARK_PATH_LENGTH * (1 - drawProgress);

  return (
    <div
      style={{
        position: 'absolute',
        left: DIMENSIONS.checkmarkCenterX - DIMENSIONS.checkmarkSize / 2,
        top: DIMENSIONS.checkmarkCenterY - DIMENSIONS.checkmarkSize / 2,
        width: DIMENSIONS.checkmarkSize,
        height: DIMENSIONS.checkmarkSize,
      }}
    >
      <svg
        width={DIMENSIONS.checkmarkSize}
        height={DIMENSIONS.checkmarkSize}
        viewBox="0 0 48 48"
        fill="none"
      >
        <path
          d={CHECKMARK_PATH}
          stroke={COLORS.checkmark}
          strokeWidth={DIMENSIONS.checkmarkStrokeWidth}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={CHECKMARK_PATH_LENGTH}
          strokeDashoffset={dashOffset}
        />
      </svg>
    </div>
  );
};
