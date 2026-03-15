import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, SHAPE, TIMING } from './constants';

export const PulsingTriangle: React.FC = () => {
  const frame = useCurrentFrame();

  // Phase 1 (frames 0-5): Fade in with opacity 0→1
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

  // Determine current size based on animation phase
  let size: number;

  if (frame <= TIMING.pulse1ExpandStart) {
    // Phase 1: constant baseSize during fade-in
    size = SHAPE.baseSize;
  } else if (frame <= TIMING.pulse1ExpandEnd) {
    // Phase 2 (frames 5-12): First pulse expand — 120→160
    size = interpolate(
      frame,
      [TIMING.pulse1ExpandStart, TIMING.pulse1ExpandEnd],
      [SHAPE.baseSize, SHAPE.pulse1Size],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.sin),
      }
    );
  } else if (frame <= TIMING.pulse1ContractEnd) {
    // Phase 3 (frames 12-18): First pulse contract — 160→120
    size = interpolate(
      frame,
      [TIMING.pulse1ContractStart, TIMING.pulse1ContractEnd],
      [SHAPE.pulse1Size, SHAPE.baseSize],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.in(Easing.sin),
      }
    );
  } else if (frame <= TIMING.pulse2ExpandEnd) {
    // Phase 4 (frames 18-24): Second pulse expand — 120→156
    size = interpolate(
      frame,
      [TIMING.pulse2ExpandStart, TIMING.pulse2ExpandEnd],
      [SHAPE.baseSize, SHAPE.pulse2Size],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.sin),
      }
    );
  } else {
    // Phase 5 (frames 24-30): Second pulse contract — 156→120
    size = interpolate(
      frame,
      [TIMING.pulse2ContractStart, TIMING.pulse2ContractEnd],
      [SHAPE.pulse2Size, SHAPE.baseSize],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.in(Easing.sin),
      }
    );
  }

  return (
    <div
      style={{
        position: 'absolute',
        width: size,
        height: size,
        clipPath: 'polygon(50% 0%, 0% 100%, 100% 100%)',
        backgroundColor: COLORS.shapeFill,
        opacity,
        top: CANVAS.centerY - size / 2,
        left: CANVAS.centerX - size / 2,
      }}
    />
  );
};
