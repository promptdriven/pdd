import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION, CANVAS } from './constants';

export const GradientBar: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION.gradientFadeStart, ANIMATION.gradientFadeEnd],
    [0.4, ANIMATION.gradientMaxOpacity],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
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
