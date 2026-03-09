import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const RadialGlow: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.backgroundFadeStart, ANIMATION_TIMING.backgroundFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: '50%',
        transform: 'translate(-50%, -50%)',
        width: DIMENSIONS.radialGlowDiameter,
        height: DIMENSIONS.radialGlowDiameter,
        borderRadius: '50%',
        background: `radial-gradient(circle, ${COLORS.radialGlowCenter} 0%, transparent 70%)`,
        opacity,
      }}
    />
  );
};
