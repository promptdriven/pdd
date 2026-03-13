import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION_TIMING } from './constants';

export const FadeToBlack: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade to black over frames 15-21 with easeInQuad
  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.fadeOutStart, ANIMATION_TIMING.fadeOutEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
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
