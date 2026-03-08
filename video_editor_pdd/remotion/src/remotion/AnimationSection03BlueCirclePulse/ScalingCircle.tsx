import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, CIRCLE, ANIMATION_TIMING } from './constants';

export const ScalingCircle: React.FC = () => {
  const frame = useCurrentFrame();

  // Phase 1: Scale in from 0 to 1 (frames 0-15) with easeOutBack
  const scaleIn = interpolate(
    frame,
    [ANIMATION_TIMING.scaleInStart, ANIMATION_TIMING.scaleInEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.7)),
    }
  );

  // Phase 1: Opacity fade in
  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.scaleInStart, ANIMATION_TIMING.scaleInEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Phase 3: Pulse — scale up to 180/160=1.125 then back to 1.0
  const pulseUp = interpolate(
    frame,
    [ANIMATION_TIMING.pulseStart, ANIMATION_TIMING.pulsePeak],
    [1, CIRCLE.pulseRadius / CIRCLE.radius],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const pulseDown = interpolate(
    frame,
    [ANIMATION_TIMING.pulsePeak, ANIMATION_TIMING.pulseEnd],
    [CIRCLE.pulseRadius / CIRCLE.radius, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  // Phase 5: Subtle breathing (frames 35-60), scale 1.0 to 1.02 loop
  const breathingProgress = interpolate(
    frame,
    [ANIMATION_TIMING.breathingStart, ANIMATION_TIMING.breathingEnd],
    [0, Math.PI * 2],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );
  const breathingScale = frame >= ANIMATION_TIMING.breathingStart
    ? 1 + 0.02 * Math.sin(breathingProgress)
    : 1;

  // Combine scale phases
  let scale = scaleIn;
  if (frame >= ANIMATION_TIMING.pulseStart && frame < ANIMATION_TIMING.pulsePeak) {
    scale = scaleIn * pulseUp;
  } else if (frame >= ANIMATION_TIMING.pulsePeak && frame < ANIMATION_TIMING.pulseEnd) {
    scale = scaleIn * pulseDown;
  } else if (frame >= ANIMATION_TIMING.breathingStart) {
    scale = scaleIn * breathingScale;
  }

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.centerX - CIRCLE.radius,
        top: CANVAS.centerY - CIRCLE.radius,
        width: CIRCLE.diameter,
        height: CIRCLE.diameter,
        borderRadius: '50%',
        backgroundColor: COLORS.circleFill,
        opacity,
        transform: `scale(${scale})`,
        boxShadow: `0 0 30px ${COLORS.circleFill}40`,
      }}
    />
  );
};
