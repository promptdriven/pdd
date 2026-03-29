import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { ELLIPSIS_CYCLE_FRAMES, FADE_IN_DURATION } from './constants';

interface PulsingEllipsisProps {
  color: string;
  appearFrame: number;
}

export const PulsingEllipsis: React.FC<PulsingEllipsisProps> = ({ color, appearFrame }) => {
  const frame = useCurrentFrame();

  // Initial fade-in
  const baseOpacity = interpolate(
    frame,
    [appearFrame, appearFrame + FADE_IN_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Each dot pulses with staggered timing
  const dots = [0, 1, 2].map((dotIndex) => {
    if (frame < appearFrame + FADE_IN_DURATION) {
      return baseOpacity;
    }
    const offset = dotIndex * 6; // stagger by 6 frames
    const cycleFrame = (frame - appearFrame - FADE_IN_DURATION + offset) % ELLIPSIS_CYCLE_FRAMES;
    const pulseOpacity = interpolate(
      cycleFrame,
      [0, ELLIPSIS_CYCLE_FRAMES / 2, ELLIPSIS_CYCLE_FRAMES],
      [0.3, 0.9, 0.3],
      { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.sin) }
    );
    return pulseOpacity;
  });

  return (
    <div style={{ display: 'flex', gap: 6, justifyContent: 'center', alignItems: 'center', height: 20 }}>
      {dots.map((dotOpacity, i) => (
        <div
          key={i}
          style={{
            width: 8,
            height: 8,
            borderRadius: '50%',
            backgroundColor: color,
            opacity: dotOpacity,
          }}
        />
      ))}
    </div>
  );
};

export default PulsingEllipsis;
