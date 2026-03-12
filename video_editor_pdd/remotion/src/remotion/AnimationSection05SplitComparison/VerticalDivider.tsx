import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const VerticalDivider: React.FC = () => {
  const frame = useCurrentFrame();

  const halfHeight = interpolate(
    frame,
    [ANIMATION_TIMING.dividerDrawStart, ANIMATION_TIMING.dividerDrawEnd],
    [0, CANVAS.height / 2],
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
        left: CANVAS.width / 2 - DIMENSIONS.dividerWidth / 2,
        top: CANVAS.height / 2 - halfHeight,
        width: DIMENSIONS.dividerWidth,
        height: halfHeight * 2,
        backgroundColor: COLORS.divider,
        opacity: DIMENSIONS.dividerOpacity,
      }}
    />
  );
};
