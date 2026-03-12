import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const DrawCheckmark: React.FC = () => {
  const frame = useCurrentFrame();

  // The checkmark has two strokes: short left leg and longer right leg
  // Total path length for a checkmark in a 40px box
  // Path: M 8,20 L 16,28 L 32,12
  // Left leg length ≈ 11.3, Right leg length ≈ 22.6, total ≈ 33.9
  const totalPathLength = 34;

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

  const dashOffset = totalPathLength * (1 - drawProgress);

  // Only show after line contracts
  const opacity = frame >= ANIMATION_TIMING.checkmarkDrawStart ? 1 : 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: 340,
        transform: 'translate(-50%, -50%)',
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
          d="M 8 20 L 16 28 L 32 12"
          stroke={COLORS.checkmark}
          strokeWidth={DIMENSIONS.checkmarkStrokeWidth}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={totalPathLength}
          strokeDashoffset={dashOffset}
        />
      </svg>
    </div>
  );
};
