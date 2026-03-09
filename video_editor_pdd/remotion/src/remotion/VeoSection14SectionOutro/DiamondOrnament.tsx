import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, POSITIONS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const DiamondOrnament: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.diamondStart, ANIMATION_TIMING.diamondEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  // Rotate from 0 to 45 degrees with easeOutBack
  const rotation = interpolate(
    frame,
    [ANIMATION_TIMING.diamondStart, ANIMATION_TIMING.diamondEnd],
    [0, 45],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.7)),
    },
  );

  if (opacity <= 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        top: POSITIONS.diamondY - DIMENSIONS.diamondSize / 2,
        left: CANVAS.width / 2 - DIMENSIONS.diamondSize / 2,
        width: DIMENSIONS.diamondSize,
        height: DIMENSIONS.diamondSize,
        backgroundColor: COLORS.diamond,
        opacity,
        transform: `rotate(${rotation}deg)`,
      }}
    />
  );
};
