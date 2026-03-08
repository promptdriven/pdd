import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, POSITIONS, DIMENSIONS, ANIMATION } from './constants';

export const DividerWipe: React.FC = () => {
  const frame = useCurrentFrame();

  const height = interpolate(
    frame,
    [ANIMATION.dividerWipeStart, ANIMATION.dividerWipeEnd],
    [0, CANVAS.height],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: POSITIONS.dividerX - DIMENSIONS.dividerWidth / 2,
        top: 0,
        width: DIMENSIONS.dividerWidth,
        height,
        backgroundColor: COLORS.divider,
        zIndex: 10,
      }}
    />
  );
};
