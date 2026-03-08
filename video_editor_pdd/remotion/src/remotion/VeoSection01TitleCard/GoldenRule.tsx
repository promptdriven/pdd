import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, POSITIONS, ANIMATION_TIMING } from './constants';

export const GoldenRule: React.FC = () => {
  const frame = useCurrentFrame();

  const scaleX = interpolate(
    frame,
    [ANIMATION_TIMING.ruleFadeStart, ANIMATION_TIMING.ruleFadeEnd],
    [0, 1],
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
        top: POSITIONS.accentLineY,
        left: '50%',
        transform: `translateX(-50%) scaleX(${scaleX})`,
        width: DIMENSIONS.accentLineWidth,
        height: DIMENSIONS.accentLineHeight,
        backgroundColor: COLORS.accentLine,
        boxShadow: `0 0 20px ${COLORS.accentLine}40`,
      }}
    />
  );
};
