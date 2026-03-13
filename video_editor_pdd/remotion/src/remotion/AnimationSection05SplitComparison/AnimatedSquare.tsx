import React from 'react';
import { useCurrentFrame, spring } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING, SHAPE_SPRING_CONFIG } from './constants';

export const AnimatedSquare: React.FC = () => {
  const frame = useCurrentFrame();

  // Spring scale-in starting at squareScaleStart (frame 10, 2-frame stagger)
  const scaleIn = spring({
    frame: frame - ANIMATION_TIMING.squareScaleStart,
    fps: 30,
    config: SHAPE_SPRING_CONFIG,
  });

  // Breathing animation after breathingStart (frame 20), in phase with circle
  let breathingScale = 1;
  if (frame >= ANIMATION_TIMING.breathingStart) {
    const breathFrame = frame - ANIMATION_TIMING.breathingStart;
    const t = (breathFrame % ANIMATION_TIMING.breathingCycleFrames) / ANIMATION_TIMING.breathingCycleFrames;
    const amplitude = (ANIMATION_TIMING.breathingScaleMax - ANIMATION_TIMING.breathingScaleMin) / 2;
    breathingScale = 1 + amplitude * (1 - Math.cos(2 * Math.PI * t));
  }

  const finalScale = frame >= ANIMATION_TIMING.squareScaleStart
    ? scaleIn * breathingScale
    : 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: 960 - DIMENSIONS.squareSize / 2,
        top: DIMENSIONS.shapeCenterY - DIMENSIONS.squareSize / 2,
        width: DIMENSIONS.squareSize,
        height: DIMENSIONS.squareSize,
        borderRadius: DIMENSIONS.squareBorderRadius,
        backgroundColor: COLORS.square,
        transform: `scale(${finalScale})`,
      }}
    />
  );
};
