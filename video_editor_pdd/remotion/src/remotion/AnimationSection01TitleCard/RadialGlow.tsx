import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS } from './constants';

export const RadialGlow: React.FC = () => {
  const frame = useCurrentFrame();

  // Radius: 300 -> 400 (0-5), 400 -> 500 (20-25), 500 -> 400 (25-33)
  const radius = interpolate(
    frame,
    [0, 5, 22, 33],
    [
      DIMENSIONS.glowInitialRadius,
      DIMENSIONS.glowExpandedRadius,
      DIMENSIONS.glowPulseRadius,
      DIMENSIONS.glowRestingRadius,
    ],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  // Opacity: 0 -> 0.4 (0-5), 0.4 -> 0.5 (5-22), 0.5 -> 0.35 (22-33)
  const opacity = interpolate(
    frame,
    [0, 5, 22, 33],
    [
      DIMENSIONS.glowInitialOpacity,
      DIMENSIONS.glowExpandedOpacity,
      DIMENSIONS.glowPulseOpacity,
      DIMENSIONS.glowRestingOpacity,
    ],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  const diameter = radius * 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: '50%',
        transform: 'translate(-50%, -50%)',
        width: diameter,
        height: diameter,
        borderRadius: '50%',
        background: `radial-gradient(circle, ${COLORS.glowCenter} 0%, transparent 70%)`,
        opacity,
      }}
    />
  );
};
