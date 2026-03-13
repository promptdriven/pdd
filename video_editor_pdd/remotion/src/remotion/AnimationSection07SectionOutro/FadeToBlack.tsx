import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION_TIMING } from './constants';

export const FadeToBlack: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.fadeToBlackStart, ANIMATION_TIMING.fadeToBlackEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.cubic),
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
