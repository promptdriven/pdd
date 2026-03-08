import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS } from './constants';

const PULSE_PERIOD = 40;

export const StatusIndicator: React.FC = () => {
  const frame = useCurrentFrame();

  const pulsePhase = (frame % PULSE_PERIOD) / PULSE_PERIOD;
  const pulseScale = interpolate(
    pulsePhase,
    [0, 0.5, 1],
    [1, 2, 1],
  );
  const pulseOpacity = interpolate(
    pulsePhase,
    [0, 0.5, 1],
    [0.5, 0, 0.5],
  );

  return (
    <div
      style={{
        position: 'relative',
        width: 10,
        height: 10,
        flexShrink: 0,
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
