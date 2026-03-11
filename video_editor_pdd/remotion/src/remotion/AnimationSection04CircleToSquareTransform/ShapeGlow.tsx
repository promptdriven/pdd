import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { SHAPE, GLOW, TIMING, COLORS } from './constants';

/**
 * Renders a soft glow that tracks behind the main shape,
 * matching its current color and position.
 */
export const ShapeGlow: React.FC = () => {
  const frame = useCurrentFrame();

  // Position (same easing as main shape slide)
  const currentX = interpolate(
    frame,
    [TIMING.slideStart, TIMING.slideEnd],
    [SHAPE.startX, SHAPE.endX],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.poly(4) },
  );

  // Color interpolation
  const colorProgress = interpolate(
    frame,
    [TIMING.colorStart, TIMING.colorEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  const r = Math.round(236 + (34 - 236) * colorProgress);
  const g = Math.round(72 + (197 - 72) * colorProgress);
  const b = Math.round(153 + (94 - 153) * colorProgress);
  const currentColor = `rgb(${r}, ${g}, ${b})`;

  return (
    <div
      style={{
        position: 'absolute',
        width: SHAPE.size,
        height: SHAPE.size,
        left: currentX - SHAPE.size / 2,
        top: SHAPE.cy - SHAPE.size / 2,
        borderRadius: '50%',
        backgroundColor: currentColor,
        opacity: GLOW.opacity,
        filter: `blur(${GLOW.blur}px)`,
      }}
    />
  );
};
