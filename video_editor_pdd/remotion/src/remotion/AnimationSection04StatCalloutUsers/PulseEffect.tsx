/**
 * PulseEffect component
 * Wraps children with a subtle pulse animation (scale 1.0 → 1.03 → 1.0)
 */

import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';

interface PulseEffectProps {
  children: React.ReactNode;
}

export const PulseEffect: React.FC<PulseEffectProps> = ({ children }) => {
  const frame = useCurrentFrame();

  // Pulse animation with easeInOutSine
  const progress = interpolate(
    frame,
    [0, 15],
    [0, 1],
    {
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  // Scale from 1.0 → 1.03 → 1.0
  const scale = progress < 0.5
    ? 1.0 + (progress * 2 * 0.03)
    : 1.03 - ((progress - 0.5) * 2 * 0.03);

  return (
    <div
      style={{
        position: 'absolute',
        width: '100%',
        height: '100%',
        transform: `scale(${scale})`,
      }}
    >
      {children}
    </div>
  );
};
