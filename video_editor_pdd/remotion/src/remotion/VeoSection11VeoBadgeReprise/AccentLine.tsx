import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, POSITIONS, DIMENSIONS, ANIMATION } from './constants';

export const AccentLine: React.FC = () => {
  const frame = useCurrentFrame();

  // Expand: frames 35-45, easeInOutQuad
  const width = interpolate(
    frame,
    [ANIMATION.accentLineStart, ANIMATION.accentLineEnd],
    [0, DIMENSIONS.accentLineWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.poly(2)),
    },
  );

  // Fade out: frames 75-90
  const opacity = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.poly(2)),
    },
  );

  // Don't render before expand starts
  const lineOpacity = frame < ANIMATION.accentLineStart ? 0 : opacity;

  return (
    <div
      style={{
        position: 'absolute',
        top: POSITIONS.accentLineY,
        left: POSITIONS.center - width / 2,
        width,
        height: DIMENSIONS.accentLineHeight,
        backgroundColor: COLORS.accent,
        opacity: lineOpacity,
      }}
    />
  );
};
