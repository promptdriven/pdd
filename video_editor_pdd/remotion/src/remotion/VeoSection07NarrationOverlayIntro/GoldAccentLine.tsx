import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, BASE_CANVAS } from './constants';

export const GoldAccentLine: React.FC = () => {
  const frame = useCurrentFrame();

  // Frame 8–10: Fade in opacity 0→1
  const opacity = interpolate(
    frame,
    [ANIMATION.accentFadeStart, ANIMATION.accentFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: BASE_CANVAS.width,
        height: 2,
        backgroundColor: COLORS.gold,
        opacity,
      }}
    />
  );
};
