import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, CIRCLE, TIMING } from './constants';

export const PulsingCircle: React.FC = () => {
  const frame = useCurrentFrame();

  // Phase 1 (frames 0-5): Scale in from 0 to baseRadius with easeOutBack
  const appearScale = interpolate(
    frame,
    [TIMING.appearStart, TIMING.appearEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.7)),
    }
  );

  // Pulse helper: maps a frame range to baseRadius → pulseRadius → baseRadius
  const getPulseRadius = (
    start: number,
    end: number,
    currentFrame: number
  ): number => {
    const mid = (start + end) / 2;
    if (currentFrame <= mid) {
      return interpolate(currentFrame, [start, mid], [CIRCLE.baseRadius, CIRCLE.pulseRadius], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      });
    }
    return interpolate(currentFrame, [mid, end], [CIRCLE.pulseRadius, CIRCLE.baseRadius], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    });
  };

  // Determine current radius based on animation phase
  let radius: number;
  if (frame < TIMING.appearEnd) {
    radius = CIRCLE.baseRadius * appearScale;
  } else if (frame < TIMING.pulse1End) {
    radius = getPulseRadius(TIMING.pulse1Start, TIMING.pulse1End, frame);
  } else if (frame < TIMING.contract1End) {
    // Contract phase is integrated into pulse1 already via mid-point logic,
    // but the spec defines separate contract. Map frames 15-20 as contraction.
    radius = interpolate(frame, [TIMING.contract1Start, TIMING.contract1End], [CIRCLE.pulseRadius, CIRCLE.baseRadius], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    });
  } else if (frame < TIMING.holdStart) {
    radius = getPulseRadius(TIMING.pulse2Start, TIMING.pulse2End, frame);
  } else {
    radius = CIRCLE.baseRadius;
  }

  const diameter = radius * 2;

  return (
    <div
      style={{
        position: 'absolute',
        width: diameter,
        height: diameter,
        borderRadius: '50%',
        backgroundColor: COLORS.circleFill,
        top: CANVAS.centerY - radius,
        left: CANVAS.centerX - radius,
      }}
    />
  );
};
