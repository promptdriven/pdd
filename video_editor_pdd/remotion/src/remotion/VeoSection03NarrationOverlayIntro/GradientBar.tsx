import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING, CANVAS } from './constants';

export const GradientBar: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.gradientFadeStart, ANIMATION_TIMING.gradientFadeEnd],
    [0, 0.9],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        bottom: 0,
        left: 0,
        width: CANVAS.width,
        height: DIMENSIONS.gradientBarHeight,
        background: `linear-gradient(180deg, ${COLORS.gradientFrom} 0%, ${COLORS.gradientTo} 100%)`,
        opacity,
      }}
    />
  );
};
