import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, ANIMATION } from './constants';

export const StatusDot: React.FC<{ x: number; y: number }> = ({ x, y }) => {
  const frame = useCurrentFrame();

  const pulsePhase = (frame % ANIMATION.dotPulsePeriod) / ANIMATION.dotPulsePeriod;
  const pulseScale = interpolate(
    pulsePhase,
    [0, 0.5, 1],
    [1, 1.8, 1],
  );
  const pulseOpacity = interpolate(
    pulsePhase,
    [0, 0.5, 1],
    [0.6, 0, 0.6],
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        width: 10,
        height: 10,
      }}
    >
      {/* Pulse ring */}
      <div
        style={{
          position: 'absolute',
          left: -5,
          top: -5,
          width: 20,
          height: 20,
          borderRadius: '50%',
          backgroundColor: COLORS.dotPulse,
          transform: `scale(${pulseScale})`,
          opacity: pulseOpacity,
        }}
      />
      {/* Core dot */}
      <div
        style={{
          position: 'absolute',
          left: 0,
          top: 0,
          width: 10,
          height: 10,
          borderRadius: '50%',
          backgroundColor: COLORS.dotActive,
          boxShadow: `0 0 8px ${COLORS.dotPulse}`,
        }}
      />
    </div>
  );
};
