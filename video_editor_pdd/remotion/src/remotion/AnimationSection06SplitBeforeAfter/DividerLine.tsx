import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const DividerLine: React.FC = () => {
  const frame = useCurrentFrame();

  const height = interpolate(
    frame,
    [ANIMATION_TIMING.dividerStart, ANIMATION_TIMING.dividerEnd],
    [0, CANVAS.height],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.dividerX - DIMENSIONS.dividerWidth / 2,
        top: 0,
        width: DIMENSIONS.dividerWidth,
        height,
        backgroundColor: COLORS.divider,
        boxShadow: `0 0 ${DIMENSIONS.dividerGlowBlur}px rgba(59, 130, 246, 0.3)`,
        zIndex: 10,
      }}
    />
  );
};
