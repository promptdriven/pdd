import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING, POSITIONS } from './constants';

export const AccentLine: React.FC = () => {
  const frame = useCurrentFrame();

  const scaleX = interpolate(
    frame,
    [ANIMATION_TIMING.accentLineStart, ANIMATION_TIMING.accentLineEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: POSITIONS.accentLineY,
        left: '50%',
        transform: `translateX(-50%) scaleX(${scaleX})`,
        width: DIMENSIONS.accentLineWidth,
        height: DIMENSIONS.accentLineHeight,
        backgroundColor: COLORS.accent,
      }}
    />
  );
};
