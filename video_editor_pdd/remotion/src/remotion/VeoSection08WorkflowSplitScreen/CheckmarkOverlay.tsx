/**
 * CheckmarkOverlay - Animated checkmarks for completed steps
 */

import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

interface CheckmarkOverlayProps {
  x: number;
  y: number;
  startFrame: number;
  color: string;
}

export const CheckmarkOverlay: React.FC<CheckmarkOverlayProps> = ({
  x,
  y,
  startFrame,
  color,
}) => {
  const frame = useCurrentFrame();

  const scale = interpolate(
    frame - startFrame,
    [0, 15],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const opacity = interpolate(
    frame - startFrame,
    [0, 10],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  const rotation = interpolate(
    frame - startFrame,
    [0, 15],
    [-20, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        transform: `translate(-50%, -50%) scale(${scale}) rotate(${rotation}deg)`,
        opacity,
        fontSize: 48,
        color,
        pointerEvents: 'none',
      }}
    >
      ✓
    </div>
  );
};
