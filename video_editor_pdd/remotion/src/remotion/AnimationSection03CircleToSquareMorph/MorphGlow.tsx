import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { TIMING, MORPH, DIMENSIONS } from './constants';

export const MorphGlow: React.FC = () => {
  const frame = useCurrentFrame();

  // Glow rises from 0 → 0.25 opacity (frame 5–15)
  const glowIn = interpolate(
    frame,
    [TIMING.morphStart, TIMING.glowPeak],
    [0, MORPH.glowPeakOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Glow fades 0.25 → 0 (frame 15–25)
  const glowOut = interpolate(
    frame,
    [TIMING.glowPeak, TIMING.morphEnd],
    [MORPH.glowPeakOpacity, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.quad),
    }
  );

  let opacity: number;
  if (frame < TIMING.morphStart) {
    opacity = 0;
  } else if (frame <= TIMING.glowPeak) {
    opacity = glowIn;
  } else if (frame <= TIMING.morphEnd) {
    opacity = glowOut;
  } else {
    opacity = 0;
  }

  return (
    <div
      style={{
        position: 'absolute',
        width: DIMENSIONS.glowSpread,
        height: DIMENSIONS.glowSpread,
        borderRadius: '50%',
        background:
          'radial-gradient(circle, rgba(255, 255, 255, 0.6) 0%, rgba(255, 255, 255, 0.1) 50%, transparent 100%)',
        opacity,
        filter: 'blur(40px)',
        top: '50%',
        left: '50%',
        transform: 'translate(-50%, -50%)',
      }}
    />
  );
};
