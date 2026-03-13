import React from 'react';
import { useCurrentFrame, spring } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING, SHAPE_SPRING_CONFIG } from './constants';

export const AnimatedCircle: React.FC = () => {
  const frame = useCurrentFrame();

  // Spring scale-in starting at circleScaleStart (frame 8)
  const scaleIn = spring({
    frame: frame - ANIMATION_TIMING.circleScaleStart,
    fps: 30,
    config: SHAPE_SPRING_CONFIG,
  });

  // Breathing animation after breathingStart (frame 20)
  let breathingScale = 1;
  if (frame >= ANIMATION_TIMING.breathingStart) {
    const breathFrame = frame - ANIMATION_TIMING.breathingStart;
    const t = (breathFrame % ANIMATION_TIMING.breathingCycleFrames) / ANIMATION_TIMING.breathingCycleFrames;
    const amplitude = (ANIMATION_TIMING.breathingScaleMax - ANIMATION_TIMING.breathingScaleMin) / 2;
    breathingScale = 1 + amplitude * (1 - Math.cos(2 * Math.PI * t));
  }

  const finalScale = frame >= ANIMATION_TIMING.circleScaleStart
    ? scaleIn * breathingScale
    : 0;

  return (
    <div
      style={{
        position: 'absolute',
        left: 320 - DIMENSIONS.circleDiameter / 2,
        top: DIMENSIONS.shapeCenterY - DIMENSIONS.circleDiameter / 2,
        width: DIMENSIONS.circleDiameter,
        height: DIMENSIONS.circleDiameter,
        borderRadius: '50%',
        backgroundColor: COLORS.circle,
        transform: `scale(${finalScale})`,
      }}
    />
  );
};
