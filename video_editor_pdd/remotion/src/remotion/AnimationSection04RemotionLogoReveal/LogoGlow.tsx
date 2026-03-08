import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { COLORS, LOGO, TIMING } from './constants';

export const LogoGlow: React.FC = () => {
  const frame = useCurrentFrame();

  const glowOpacity = interpolate(
    frame,
    [TIMING.glowStart, TIMING.glowPeak, TIMING.glowEnd],
    [0, 0.6, 0.25],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  const glowScale = interpolate(
    frame,
    [TIMING.glowStart, TIMING.glowPeak, TIMING.glowEnd],
    [0.8, 1.3, 1.0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: LOGO.cx - 200,
        top: LOGO.cy - 200,
        width: 400,
        height: 400,
        borderRadius: '50%',
        background: `radial-gradient(circle, ${COLORS.glowBlue} 0%, transparent 70%)`,
        opacity: glowOpacity,
        transform: `scale(${glowScale})`,
      }}
    />
  );
};
