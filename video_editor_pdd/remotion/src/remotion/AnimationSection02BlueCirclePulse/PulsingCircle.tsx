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

  // Determine current radius based on animation phase
  let radius: number;
  if (frame < TIMING.appearEnd) {
    // Phase 1: appear from 0 to baseRadius
    radius = CIRCLE.baseRadius * appearScale;
  } else if (frame < TIMING.contract1Start) {
    // Phase 2 (frames 5-15): First pulse expansion — 60px to 80px
    radius = interpolate(
      frame,
      [TIMING.pulse1Start, TIMING.pulse1End],
      [CIRCLE.baseRadius, CIRCLE.pulseRadius],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      }
    );
  } else if (frame < TIMING.pulse2Start) {
    // Phase 3 (frames 15-20): Contract back from 80px to 60px
    radius = interpolate(
      frame,
      [TIMING.contract1Start, TIMING.contract1End],
      [CIRCLE.pulseRadius, CIRCLE.baseRadius],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.inOut(Easing.sin),
      }
    );
  } else if (frame < TIMING.holdStart) {
    // Phase 4 (frames 20-28): Second pulse — expand then contract
    const mid = (TIMING.pulse2Start + TIMING.pulse2End) / 2;
    if (frame <= mid) {
      radius = interpolate(
        frame,
        [TIMING.pulse2Start, mid],
        [CIRCLE.baseRadius, CIRCLE.pulseRadius],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.inOut(Easing.sin),
        }
      );
    } else {
      radius = interpolate(
        frame,
        [mid, TIMING.pulse2End],
        [CIRCLE.pulseRadius, CIRCLE.baseRadius],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.inOut(Easing.sin),
        }
      );
    }
  } else {
    // Phase 5 (frames 28-30): Hold at baseRadius
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
