import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
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
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
        backgroundColor: COLORS.fadeToBlack,
        opacity,
      }}
    />
  );
};
