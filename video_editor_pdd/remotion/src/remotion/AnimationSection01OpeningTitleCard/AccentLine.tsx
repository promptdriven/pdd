import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, CANVAS } from './constants';

export const AccentLine: React.FC = () => {
  const frame = useCurrentFrame();

  const width = interpolate(
    frame,
    [0, 15],
    [0, DIMENSIONS.accentLineWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const centerX = CANVAS.width / 2;
  const left = centerX - width / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left,
        top: DIMENSIONS.accentLineY,
        width,
        height: DIMENSIONS.accentLineHeight,
        backgroundColor: COLORS.accentBlue,
      }}
    />
  );
};
