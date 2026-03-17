import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { PULSE_COLOR, PULSE_OPACITY, PULSE_PERIOD } from './constants';

export const PulseGlow: React.FC = () => {
  const frame = useCurrentFrame();

  // Sine-based pulse on 60-frame cycle
  const cycleProgress = (frame % PULSE_PERIOD) / PULSE_PERIOD;
  const pulseValue = interpolate(
    cycleProgress,
    [0, 0.5, 1],
    [0, 1, 0],
    { easing: Easing.inOut(Easing.sin) }
  );

  const opacity = PULSE_OPACITY + pulseValue * 0.015;

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
        background: `radial-gradient(ellipse 600px 600px at 960px 540px, ${PULSE_COLOR}, transparent)`,
        opacity,
        pointerEvents: 'none',
      }}
    />
  );
};
