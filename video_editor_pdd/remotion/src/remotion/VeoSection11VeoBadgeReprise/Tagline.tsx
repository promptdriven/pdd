import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, POSITIONS, ANIMATION, TAGLINE_TEXT } from './constants';

export const Tagline: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in: frames 25-40, easeOutCubic
  const opacityIn = interpolate(
    frame,
    [ANIMATION.taglineStart, ANIMATION.taglineEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  // Slide up: Y 580 → 560
  const posY = interpolate(
    frame,
    [ANIMATION.taglineStart, ANIMATION.taglineEnd],
    [POSITIONS.taglineStartY, POSITIONS.taglineEndY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  // Fade out: frames 75-90
  const opacityOut = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.poly(2)),
    },
  );

  const opacity = Math.min(opacityIn, opacityOut);

  return (
    <div
      style={{
        position: 'absolute',
        top: posY,
        left: 0,
        width: '100%',
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'center',
        opacity,
      }}
    >
      <span
        style={{
          color: COLORS.accent,
          fontSize: TYPOGRAPHY.tagline.fontSize,
          fontFamily: TYPOGRAPHY.tagline.fontFamily,
          fontWeight: TYPOGRAPHY.tagline.fontWeight,
          letterSpacing: TYPOGRAPHY.tagline.letterSpacing,
          lineHeight: 1,
        }}
      >
        {TAGLINE_TEXT}
      </span>
    </div>
  );
};
