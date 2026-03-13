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

  // --- Border Radius: 90px (circle) → 8px (rounded square) ---
  const borderRadius = interpolate(
    frame,
    [TIMING.morphStart, TIMING.morphEnd],
    [DIMENSIONS.circleBorderRadius, DIMENSIONS.squareBorderRadius],
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
    [COLORS.circleBlue, COLORS.squareGreen]
  );

  // --- Size: 180px → 160px ---
  const size = interpolate(
    frame,
    [TIMING.morphStart, TIMING.morphEnd],
    [DIMENSIONS.circleSize, DIMENSIONS.squareSize],
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
    [0, MORPH.rotationDeg],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  // --- Scale ---
  // Phase 1 (frames 0-5): Subtle breathing via sine curve (1.0 → 1.02)
  const breathingProgress = interpolate(
    frame,
    [TIMING.holdStart, TIMING.holdEnd],
    [0, Math.PI],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );
  const breathingScale =
    1 + (MORPH.breathingScale - 1) * Math.sin(breathingProgress);

  // Phase 3 (frames 25-33): Spring settle with overshoot
  const settleSpring = spring({
    frame: Math.max(0, frame - TIMING.settleStart),
    fps: FPS,
    config: {
      damping: 14,
      stiffness: 200,
      mass: 1,
    },
  });
  // Spring goes 0→1 (with overshoot). Map to scale: 1.05 → 1.0
  const settleScale =
    MORPH.overshootScale - settleSpring * (MORPH.overshootScale - 1.0);

  let scale: number;
  if (frame < TIMING.morphStart) {
    scale = breathingScale;
  } else if (frame < TIMING.settleStart) {
    scale = 1.0;
  } else {
    scale = settleScale;
  }

  // --- Drop shadow color transitions from blue to green ---
  const shadowColor = interpolateColors(
    frame,
    [TIMING.morphStart, TIMING.morphEnd],
    [COLORS.blueShadow, COLORS.greenShadow]
  );

  return (
    <div
      style={{
        position: 'absolute',
        width: size,
        height: size,
        borderRadius,
        backgroundColor: fillColor,
        boxShadow: `0px 0px 40px ${shadowColor}`,
        top: '50%',
        left: '50%',
        transform: `translate(-50%, -50%) rotate(${rotation}deg) scale(${scale})`,
      }}
    />
  );
};
