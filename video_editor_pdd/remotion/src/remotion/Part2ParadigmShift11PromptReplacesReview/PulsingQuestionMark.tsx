import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS } from './constants';

export const PulsingQuestionMark: React.FC<{
  fadeInStart: number;
}> = ({ fadeInStart }) => {
  const frame = useCurrentFrame();

  const baseOpacity = interpolate(
    frame,
    [fadeInStart, fadeInStart + 20],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Pulsing between 0.15 and 0.3 on a 30-frame cycle
  const pulseFrame = Math.max(0, frame - fadeInStart);
  const pulseCycle = (pulseFrame % 30) / 30;
  const pulseT = Math.sin(pulseCycle * Math.PI * 2) * 0.5 + 0.5; // 0..1
  const pulseOpacity = 0.15 + pulseT * 0.15; // 0.15..0.30

  return (
    <div
      style={{
        position: 'absolute',
        left: 480 - 100,
        top: 450 - 100,
        width: 200,
        height: 200,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        opacity: baseOpacity,
      }}
    >
      {/* Glow */}
      <div
        style={{
          position: 'absolute',
          fontFamily: 'Inter, sans-serif',
          fontSize: 200,
          fontWeight: 700,
          color: COLORS.red,
          opacity: 0.06,
          filter: 'blur(30px)',
          userSelect: 'none',
        }}
      >
        ?
      </div>
      {/* Main character */}
      <div
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 200,
          fontWeight: 700,
          color: COLORS.red,
          opacity: pulseOpacity,
          lineHeight: 1,
          userSelect: 'none',
        }}
      >
        ?
      </div>
    </div>
  );
};
