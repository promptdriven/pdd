import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, CIRCLE, PULSE, TIMING } from './constants';

export const ScalingCircle: React.FC = () => {
  const frame = useCurrentFrame();

  // Phase 1 (0-20): Scale in from 0 to 1 with easeOutBack
  const scaleIn = interpolate(
    frame,
    [TIMING.scaleInStart, TIMING.scaleInEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.7)),
    }
  );

  // Phase 1 (0-20): Opacity fade in
  const opacity = interpolate(
    frame,
    [TIMING.scaleInStart, TIMING.scaleInEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Phase 2 (20-40): Drop shadow fades in
  const shadowOpacity = interpolate(
    frame,
    [TIMING.holdStart, TIMING.holdEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Phase 3 (40-60): Pulse — scale 1.0 → 1.15 → 1.0 with easeInOutSine
  const pulseUp = interpolate(
    frame,
    [TIMING.pulseStart, TIMING.pulsePeak],
    [1, PULSE.scaleMax],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  const pulseDown = interpolate(
    frame,
    [TIMING.pulsePeak, TIMING.pulseEnd],
    [PULSE.scaleMax, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  // Combine scale phases
  let scale = scaleIn;
  if (frame >= TIMING.pulseStart && frame < TIMING.pulsePeak) {
    scale = pulseUp;
  } else if (frame >= TIMING.pulsePeak && frame <= TIMING.pulseEnd) {
    scale = pulseDown;
  }

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.centerX - CIRCLE.radius,
        top: CANVAS.centerY - CIRCLE.radius,
        width: CIRCLE.diameter,
        height: CIRCLE.diameter,
        backgroundColor: COLORS.circleFill,
        clipPath:
          'polygon(50% 0%, 61% 35%, 98% 35%, 68% 57%, 79% 91%, 50% 70%, 21% 91%, 32% 57%, 2% 35%, 39% 35%)',
        opacity,
        transform: `scale(${scale})`,
        boxShadow: `0 4px 24px rgba(250, 204, 21, ${0.5 * shadowOpacity})`,
      }}
    />
  );
};
