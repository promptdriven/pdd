import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, PULSE, TIMING } from './constants';

export const PulseRing: React.FC = () => {
  const frame = useCurrentFrame();

  // Only visible during pulse phase (frames 40-60)
  if (frame < TIMING.pulseStart || frame > TIMING.pulseEnd) return null;

  // Ring expands from 100px radius to 150px radius with easeOutQuad
  const ringRadius = interpolate(
    frame,
    [TIMING.pulseStart, TIMING.pulseEnd],
    [PULSE.ringStartRadius, PULSE.ringEndRadius],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Opacity fades from 30% to 0%
  const opacity = interpolate(
    frame,
    [TIMING.pulseStart, TIMING.pulseEnd],
    [PULSE.ringStartOpacity, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  const diameter = ringRadius * 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.centerX - ringRadius,
        top: CANVAS.centerY - ringRadius,
        width: diameter,
        height: diameter,
        borderRadius: 0,
        border: `2px solid ${COLORS.pulseRingColor}`,
        opacity,
        pointerEvents: 'none',
      }}
    />
  );
};
