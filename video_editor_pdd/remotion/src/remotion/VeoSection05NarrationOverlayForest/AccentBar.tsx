import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const AccentBar: React.FC = () => {
  const frame = useCurrentFrame();

  const scaleY = interpolate(
    frame,
    [ANIMATION_TIMING.accentBarStart, ANIMATION_TIMING.accentBarEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.7)),
    }
  );

  const glowOpacity = interpolate(
    frame,
    [
      ANIMATION_TIMING.accentBarStart,
      ANIMATION_TIMING.accentBarEnd,
      ANIMATION_TIMING.accentBarEnd + 10,
    ],
    [0, 0.8, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: DIMENSIONS.accentBarInset,
        top: '50%',
        width: DIMENSIONS.accentBarWidth,
        height: DIMENSIONS.accentBarHeight,
        transform: `translateY(-50%) scaleY(${scaleY})`,
        backgroundColor: COLORS.accent,
        borderRadius: 2,
        boxShadow: `0 0 12px ${COLORS.accentGlow}`,
        opacity: scaleY > 0 ? 1 : 0,
      }}
    >
      <div
        style={{
          position: 'absolute',
          inset: -4,
          backgroundColor: COLORS.accent,
          borderRadius: 4,
          opacity: glowOpacity,
          filter: 'blur(8px)',
        }}
      />
    </div>
  );
};
