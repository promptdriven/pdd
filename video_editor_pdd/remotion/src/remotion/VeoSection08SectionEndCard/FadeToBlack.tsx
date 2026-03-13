import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION } from './constants';

export const FadeToBlack: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade to black (opacity 0 → 1, frames 28-37) with easeInQuad
  const opacity = interpolate(
    frame,
    [ANIMATION.fadeToBlackStart, ANIMATION.fadeToBlackEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    },
  );

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.fadeToBlack,
        opacity,
      }}
    />
  );
};
