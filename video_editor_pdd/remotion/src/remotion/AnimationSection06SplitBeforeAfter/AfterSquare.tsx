import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const AfterSquare: React.FC = () => {
  const frame = useCurrentFrame();

  const scale = interpolate(
    frame,
    [ANIMATION_TIMING.rightPanelStart, ANIMATION_TIMING.rightPanelEnd],
    [0.8, 1.0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: '50%',
        transform: `translate(-50%, -50%) scale(${scale})`,
        width: DIMENSIONS.shapeSize,
        height: DIMENSIONS.shapeSize,
        backgroundColor: COLORS.square,
        clipPath:
          'polygon(50% 0%, 61% 35%, 98% 35%, 68% 57%, 79% 91%, 50% 70%, 21% 91%, 32% 57%, 2% 35%, 39% 35%)',
      }}
    />
  );
};
