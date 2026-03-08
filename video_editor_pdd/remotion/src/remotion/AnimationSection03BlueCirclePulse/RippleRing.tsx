import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, RIPPLE, ANIMATION_TIMING } from './constants';

export const RippleRing: React.FC = () => {
  const frame = useCurrentFrame();

  if (frame < ANIMATION_TIMING.pulseStart) return null;

  // Ripple expands from startRadius to endRadius (frames 25-50)
  const rippleRadius = interpolate(
    frame,
    [ANIMATION_TIMING.pulseStart, ANIMATION_TIMING.rippleEnd],
    [RIPPLE.startRadius, RIPPLE.endRadius],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(4)),
    }
  );

  // Opacity fades from 0.6 to 0
  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.pulseStart, ANIMATION_TIMING.rippleEnd],
    [RIPPLE.startOpacity, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  const diameter = rippleRadius * 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.centerX - rippleRadius,
        top: CANVAS.centerY - rippleRadius,
        width: diameter,
        height: diameter,
        borderRadius: '50%',
        border: `${RIPPLE.strokeWidth}px solid ${COLORS.rippleStroke}`,
        opacity,
        pointerEvents: 'none',
      }}
    />
  );
};
