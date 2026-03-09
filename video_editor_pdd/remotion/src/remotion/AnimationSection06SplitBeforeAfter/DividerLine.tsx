import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const DividerLine: React.FC = () => {
  const frame = useCurrentFrame();

  const translateY = interpolate(
    frame,
    [ANIMATION_TIMING.dividerStart, ANIMATION_TIMING.dividerEnd],
    [-CANVAS.height, 0],
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
        left: CANVAS.dividerX - DIMENSIONS.dividerWidth / 2,
        top: 0,
        width: DIMENSIONS.dividerWidth,
        height: CANVAS.height,
        backgroundColor: COLORS.divider,
        transform: `translateY(${translateY}px)`,
        zIndex: 10,
      }}
    />
  );
};
