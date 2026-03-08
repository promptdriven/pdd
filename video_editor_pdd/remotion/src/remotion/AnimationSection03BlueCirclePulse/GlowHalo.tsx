import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, GLOW, ANIMATION_TIMING } from './constants';

export const GlowHalo: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.scaleInStart, ANIMATION_TIMING.scaleInEnd],
    [0, GLOW.opacity],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  const scale = interpolate(
    frame,
    [ANIMATION_TIMING.scaleInStart, ANIMATION_TIMING.scaleInEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.4)),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.centerX - GLOW.radius,
        top: CANVAS.centerY - GLOW.radius,
        width: GLOW.diameter,
        height: GLOW.diameter,
        borderRadius: '50%',
        backgroundColor: COLORS.circleFill,
        opacity,
        filter: `blur(${GLOW.blur}px)`,
        transform: `scale(${scale})`,
      }}
    />
  );
};
