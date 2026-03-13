import React from 'react';
import { useCurrentFrame, spring, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, TIMING, PULSE } from './constants';

const FPS = 30;

export const AnimatedCircle: React.FC = () => {
  const frame = useCurrentFrame();

  // Phase 1 (frames 0-8): Spring scale-in with overshoot
  const springScale = spring({
    frame,
    fps: FPS,
    config: {
      damping: 12,
      stiffness: 180,
      mass: 1,
    },
  });

  // Phase 3 (frames 15-28): Pulse beat — scale 1.0 → 1.15 → 1.0
  const pulseExpand = interpolate(
    frame,
    [TIMING.pulseStart, TIMING.pulsePeak],
    [1.0, PULSE.peakScale],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );
  const pulseContract = interpolate(
    frame,
    [TIMING.pulsePeak, TIMING.pulseEnd],
    [PULSE.peakScale, 1.0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Phase 4 (frames 28-45): Breathing oscillation 1.0–1.02
  const breathingProgress = interpolate(
    frame,
    [TIMING.breathingStart, TIMING.breathingEnd],
    [0, Math.PI * 2],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );
  const breathingScale =
    1 + (PULSE.breathingScale - 1) * Math.sin(breathingProgress);

  // Compose scale across phases
  let pulseMultiplier = 1.0;
  if (frame >= TIMING.pulseStart && frame < TIMING.pulsePeak) {
    pulseMultiplier = pulseExpand;
  } else if (frame >= TIMING.pulsePeak && frame < TIMING.pulseEnd) {
    pulseMultiplier = pulseContract;
  } else if (frame >= TIMING.breathingStart) {
    pulseMultiplier = breathingScale;
  }

  const scale = springScale * pulseMultiplier;

  // Drop shadow fades in during settle phase (frames 8-15)
  const shadowOpacity = interpolate(
    frame,
    [TIMING.settleStart, TIMING.settleEnd],
    [0, 0.3],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        width: DIMENSIONS.circleDiameter,
        height: DIMENSIONS.circleDiameter,
        backgroundColor: COLORS.circle,
        clipPath: 'polygon(50% 0%, 0% 100%, 100% 100%)',
        filter: `drop-shadow(0px 0px 40px rgba(59, 130, 246, ${shadowOpacity}))`,
        top: '50%',
        left: '50%',
        transform: `translate(-50%, -50%) scale(${scale})`,
      }}
    />
  );
};
