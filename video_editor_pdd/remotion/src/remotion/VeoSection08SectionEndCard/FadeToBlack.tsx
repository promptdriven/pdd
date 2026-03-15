import React from 'react';
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TIMING } from './constants';

export const FadeToBlack: React.FC = () => {
  const frame = useCurrentFrame();

  // Frames 41-51: Fade to black with easeInQuad
  const opacity = interpolate(
    frame,
    [TIMING.fadeStart, TIMING.fadeEnd],
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
        backgroundColor: COLORS.fadeTarget,
        opacity,
      }}
    />
  );
};
