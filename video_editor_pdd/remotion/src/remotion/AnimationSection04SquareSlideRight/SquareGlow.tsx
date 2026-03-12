import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

/**
 * A soft green glow that appears behind the square at its final resting position.
 */
export const SquareGlow: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.glowFadeInStart, ANIMATION_TIMING.glowFadeInEnd],
    [0, DIMENSIONS.glowOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  if (opacity <= 0) return null;

  const { endX, centerY, glowSize } = DIMENSIONS;

  return (
    <div
      style={{
        position: 'absolute',
        left: endX - glowSize / 2,
        top: centerY - glowSize / 2,
        width: glowSize,
        height: glowSize,
        borderRadius: '50%',
        background: `radial-gradient(circle, ${COLORS.glowColor}44 0%, transparent 70%)`,
        opacity,
        pointerEvents: 'none',
      }}
    />
  );
};
