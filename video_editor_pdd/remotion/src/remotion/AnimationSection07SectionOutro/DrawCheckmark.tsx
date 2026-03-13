import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

// Checkmark SVG path: M 8,20 L 16,28 L 32,12
// Left leg ≈ 11.3, right leg ≈ 22.6, total ≈ 34
const CHECKMARK_PATH = 'M 8 20 L 16 28 L 32 12';
const TOTAL_PATH_LENGTH = 34;

export const DrawCheckmark: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [ANIMATION_TIMING.checkmarkDrawStart, ANIMATION_TIMING.checkmarkDrawEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  const dashOffset = TOTAL_PATH_LENGTH * (1 - drawProgress);

  // Only show after divider contracts
  const opacity = frame >= ANIMATION_TIMING.checkmarkDrawStart ? 1 : 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.width / 2 - DIMENSIONS.checkmarkSize / 2,
        top: DIMENSIONS.checkmarkCenterY - DIMENSIONS.checkmarkSize / 2,
        width: DIMENSIONS.checkmarkSize,
        height: DIMENSIONS.checkmarkSize,
        opacity,
      }}
    >
      <svg
        width={DIMENSIONS.checkmarkSize}
        height={DIMENSIONS.checkmarkSize}
        viewBox="0 0 40 40"
        fill="none"
      >
        <path
          d={CHECKMARK_PATH}
          stroke={COLORS.checkmark}
          strokeWidth={DIMENSIONS.checkmarkStrokeWidth}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={TOTAL_PATH_LENGTH}
          strokeDashoffset={dashOffset}
        />
      </svg>
    </div>
  );
};
