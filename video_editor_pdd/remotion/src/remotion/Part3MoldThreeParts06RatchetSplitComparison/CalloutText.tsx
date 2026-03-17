import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { FONT_SANS, TEXT_LIGHT, GREEN } from './constants';

export const CalloutText: React.FC<{ appearFrame: number }> = ({ appearFrame }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [appearFrame, appearFrame + 20], [0, 0.7], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  // Pulse effect on "everywhere, forever"
  const pulsePhase = Math.max(0, frame - appearFrame - 20);
  const pulse = 0.7 + 0.15 * Math.sin(pulsePhase * 0.1);

  if (opacity <= 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        top: 970,
        left: 0,
        width: 1920,
        textAlign: 'center',
        fontFamily: FONT_SANS,
        fontSize: 14,
        color: TEXT_LIGHT,
        opacity,
      }}
    >
      A bug fix helps one place. A test prevents that bug{' '}
      <span style={{ fontWeight: 700, color: GREEN, opacity: pulse }}>
        everywhere, forever
      </span>
      .
    </div>
  );
};
