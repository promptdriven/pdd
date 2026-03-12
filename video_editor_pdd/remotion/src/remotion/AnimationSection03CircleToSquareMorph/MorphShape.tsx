import React from 'react';
import {
  useCurrentFrame,
  interpolate,
  interpolateColors,
  spring,
  Easing,
} from 'remotion';
import { COLORS, DIMENSIONS, TIMING, MORPH, FPS } from './constants';

export const MorphShape: React.FC = () => {
  const frame = useCurrentFrame();

  // --- Border Radius: 50% (circle) → 0% (square) ---
  const borderRadius = interpolate(
    frame,
    [TIMING.morphStart, TIMING.morphEnd],
    [50, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // --- Fill color: blue → green ---
  const fillColor = interpolateColors(
    frame,
    [TIMING.morphStart, TIMING.morphEnd],
    [COLORS.fromShape, COLORS.toShape]
  );

  // --- Size: 180px → 160px ---
  const size = interpolate(
    frame,
    [TIMING.morphStart, TIMING.morphEnd],
    [DIMENSIONS.fromSize, DIMENSIONS.toSize],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // --- Rotation: 0° → 90° ---
  const rotation = interpolate(
    frame,
    [TIMING.morphStart, TIMING.morphEnd],
    [0, MORPH.rotationDegrees],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  // --- Scale ---
  // Phase 1 (0-15): Subtle breathing 1.0 → 1.02
  const breathingScale = interpolate(
    frame,
    [TIMING.holdStart, TIMING.holdEnd],
    [1.0, MORPH.breathingScale],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  // Phase 2 (15-60): Hold at 1.0 during morph
  // Phase 3 (60-90): Spring settle with overshoot
  const settleSpring = spring({
    frame: Math.max(0, frame - TIMING.settleStart),
    fps: FPS,
    config: {
      damping: 14,
      stiffness: 200,
    },
  });
  // Spring goes 0→1, we want overshoot: 1.05 → 1.0
  const settleScale =
    MORPH.settleOvershootScale -
    settleSpring * (MORPH.settleOvershootScale - 1.0);

  let scale: number;
  if (frame < TIMING.holdEnd) {
    scale = breathingScale;
  } else if (frame < TIMING.settleStart) {
    scale = 1.0;
  } else {
    scale = settleScale;
  }

  // --- Drop shadow color blends with shape ---
  const shadowColor = interpolateColors(
    frame,
    [TIMING.morphStart, TIMING.morphEnd],
    ['rgba(59, 130, 246, 0.3)', 'rgba(34, 197, 94, 0.3)']
  );

  return (
    <div
      style={{
        position: 'absolute',
        width: size,
        height: size,
        borderRadius: `${borderRadius}%`,
        backgroundColor: fillColor,
        boxShadow: `0 4px 20px ${shadowColor}`,
        top: '50%',
        left: '50%',
        transform: `translate(-50%, -50%) scale(${scale}) rotate(${rotation}deg)`,
      }}
    />
  );
};
