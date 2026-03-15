import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TIMING } from './constants';

export const FadeToBlack: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade to black over frames 28-45 with easeInCubic
  const opacity = interpolate(
    frame,
    [TIMING.fadeStart, TIMING.fadeEnd],
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
        backgroundColor: COLORS.fadeTarget,
        opacity,
      }}
    />
  );
};
