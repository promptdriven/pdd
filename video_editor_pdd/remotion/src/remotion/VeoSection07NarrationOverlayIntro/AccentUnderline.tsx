import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, DIMENSIONS } from './constants';

export const AccentUnderline: React.FC = () => {
  const frame = useCurrentFrame();

  // Frame 18–22: Width grows from 0 → full (580px), easeInOutQuad
  const width = interpolate(
    frame,
    [ANIMATION.underlineStart, ANIMATION.underlineEnd],
    [0, DIMENSIONS.underlineMaxWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: DIMENSIONS.underlineY,
        left: '50%',
        transform: 'translateX(-50%)',
        width,
        height: DIMENSIONS.underlineHeight,
        backgroundColor: COLORS.accentUnderline,
      }}
    />
  );
};
