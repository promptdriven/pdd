import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, CIRCLE, TIMING } from './constants';

export const PulsingCircle: React.FC = () => {
  const frame = useCurrentFrame();

  // Phase 1 (frames 0-5): Fade in with opacity 0→1, radius stays at baseRadius
  const opacity = interpolate(
    frame,
    [TIMING.fadeInStart, TIMING.fadeInEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Determine current radius based on animation phase
  let radius: number;

  if (frame <= TIMING.pulse1ExpandStart) {
    // Phase 1: constant baseRadius during fade-in
    radius = CIRCLE.baseRadius;
  } else if (frame <= TIMING.pulse1ExpandEnd) {
    // Phase 2 (frames 5-12): First pulse expand — 60px → 80px
    radius = interpolate(
      frame,
      [TIMING.pulse1ExpandStart, TIMING.pulse1ExpandEnd],
      [CIRCLE.baseRadius, CIRCLE.pulse1Radius],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.sin),
      }
    );
  } else if (frame <= TIMING.pulse1ContractEnd) {
    // Phase 3 (frames 12-18): First pulse contract — 80px → 60px
    radius = interpolate(
      frame,
      [TIMING.pulse1ContractStart, TIMING.pulse1ContractEnd],
      [CIRCLE.pulse1Radius, CIRCLE.baseRadius],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.in(Easing.sin),
      }
    );
  } else if (frame <= TIMING.pulse2ExpandEnd) {
    // Phase 4 (frames 18-24): Second pulse expand — 60px → 78px
    radius = interpolate(
      frame,
      [TIMING.pulse2ExpandStart, TIMING.pulse2ExpandEnd],
      [CIRCLE.baseRadius, CIRCLE.pulse2Radius],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.sin),
      }
    );
  } else {
    // Phase 5 (frames 24-30): Second pulse contract — 78px → 60px
    radius = interpolate(
      frame,
      [TIMING.pulse2ContractStart, TIMING.pulse2ContractEnd],
      [CIRCLE.pulse2Radius, CIRCLE.baseRadius],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.in(Easing.sin),
      }
    );
  }

  const diameter = radius * 2;

  return (
    <div
      style={{
        position: 'absolute',
        width: diameter,
        height: diameter,
        clipPath: 'polygon(50% 0%, 0% 100%, 100% 100%)',
        backgroundColor: COLORS.circleFill,
        opacity,
        top: CANVAS.centerY - radius,
        left: CANVAS.centerX - radius,
      }}
    />
  );
};
