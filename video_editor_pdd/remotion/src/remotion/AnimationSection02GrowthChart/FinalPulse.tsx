import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { CHART_CONFIG, ANIMATION_TIMING } from './constants';

interface FinalPulseProps {
  children: React.ReactNode;
}

export const FinalPulse: React.FC<FinalPulseProps> = ({ children }) => {
  const frame = useCurrentFrame();
  const { start, duration } = ANIMATION_TIMING.finalPulse;

  const scale = interpolate(
    frame,
    [start, start + duration / 2, start + duration],
    [1.0, 1.02, 1.0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
        transform: `scale(${scale})`,
        transformOrigin: 'center center',
      }}
    >
      {children}
    </div>
  );
};
