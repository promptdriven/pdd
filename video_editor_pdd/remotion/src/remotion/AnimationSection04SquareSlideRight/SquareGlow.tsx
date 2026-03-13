import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, SQUARE, MOTION, TIMING, GLOW } from './constants';

/**
 * A soft green glow that appears behind the square at its final resting position.
 * Fades in during frames 27-33.
 */
export const SquareGlow: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [TIMING.fadeStart, TIMING.fadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  if (opacity <= 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        left: MOTION.targetX - SQUARE.size / 2 - 15,
        top: MOTION.centerY - SQUARE.size / 2 - 15,
        width: SQUARE.size + 30,
        height: SQUARE.size + 30,
        borderRadius: SQUARE.borderRadius + 4,
        backgroundColor: COLORS.glow,
        filter: `blur(${GLOW.blur}px)`,
        opacity,
        pointerEvents: 'none' as const,
      }}
    />
  );
};
