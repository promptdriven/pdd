import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING, POSITIONS } from './constants';

export const AccentLine: React.FC = () => {
  const frame = useCurrentFrame();

  const width = interpolate(
    frame,
    [ANIMATION_TIMING.accentLineStart, ANIMATION_TIMING.accentLineEnd],
    [0, DIMENSIONS.accentLineWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: POSITIONS.titleY + 120,
        transform: 'translateX(-50%)',
        width,
        height: DIMENSIONS.accentLineHeight,
        backgroundColor: COLORS.accentLine,
        boxShadow: `0 0 20px ${COLORS.accentLine}`,
      }}
    />
  );
};
