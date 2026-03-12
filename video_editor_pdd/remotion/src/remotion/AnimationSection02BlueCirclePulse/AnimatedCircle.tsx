import React from 'react';
import { useCurrentFrame, spring, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, TIMING, PULSE } from './constants';

const FPS = 30;

export const AnimatedCircle: React.FC = () => {
  const frame = useCurrentFrame();

  // Phase 1 (0-20): Spring scale-in with overshoot
  const springScale = spring({
    frame,
    fps: FPS,
    config: {
      damping: 12,
      stiffness: 180,
    },
  });

  // Phase 3 (50-75): Pulse beat — scale 1.0 → 1.15 → 1.0
  const pulseExpand = interpolate(
    frame,
    [TIMING.pulseStart, TIMING.pulseMid],
    [1.0, PULSE.peakScale],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );
  const pulseContract = interpolate(
    frame,
    [TIMING.pulseMid, TIMING.pulseEnd],
    [PULSE.peakScale, 1.0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  let scale: number;
  if (frame < TIMING.scaleInEnd) {
    scale = springScale;
  } else if (frame < TIMING.pulseStart) {
    scale = 1.0;
  } else if (frame <= TIMING.pulseMid) {
    scale = pulseExpand;
  } else if (frame <= TIMING.pulseEnd) {
    scale = pulseContract;
  } else {
    scale = 1.0;
  }

  return (
    <div
      style={{
        position: 'absolute',
        width: DIMENSIONS.circleDiameter,
        height: DIMENSIONS.circleDiameter,
        borderRadius: '50%',
        backgroundColor: COLORS.circle,
        boxShadow: `0 4px 20px ${COLORS.dropShadow}`,
        top: '50%',
        left: '50%',
        transform: `translate(-50%, -50%) scale(${scale})`,
      }}
    />
  );
};
