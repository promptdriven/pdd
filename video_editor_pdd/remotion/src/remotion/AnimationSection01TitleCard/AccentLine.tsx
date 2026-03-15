import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING, CANVAS, POSITIONS } from './constants';

export const AccentLine: React.FC = () => {
  const frame = useCurrentFrame();

  const width = interpolate(
    frame,
    [0, ANIMATION_TIMING.accentLineEnd - ANIMATION_TIMING.accentLineStart],
    [0, DIMENSIONS.accentLineEndWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  const left = (CANVAS.width - width) / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left,
        top: POSITIONS.accentLineY,
        width,
        height: DIMENSIONS.accentLineHeight,
        backgroundColor: COLORS.accentLine,
      }}
    />
  );
};
