import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, CANVAS, ANIMATION, DIMENSIONS } from './constants';

export const VerticalDivider: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [ANIMATION.dividerDrawStart, ANIMATION.dividerDrawEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: DIMENSIONS.dividerX - DIMENSIONS.dividerWidth / 2,
        top: 0,
        width: DIMENSIONS.dividerWidth,
        height: CANVAS.height * drawProgress,
        backgroundColor: COLORS.divider,
      }}
    />
  );
};
