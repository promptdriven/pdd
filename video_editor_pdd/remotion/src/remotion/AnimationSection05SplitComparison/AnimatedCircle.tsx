import React from 'react';
import { useCurrentFrame, spring, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING, SHAPE_SPRING_CONFIG } from './constants';

export const AnimatedCircle: React.FC = () => {
  const frame = useCurrentFrame();

  // Spring scale-in starting at circleScaleStart
  const scaleIn = spring({
    frame: frame - ANIMATION_TIMING.circleScaleStart,
    fps: 30,
    config: SHAPE_SPRING_CONFIG,
  });

  // Breathing animation after breathingStart
  let breathingScale = 1;
  if (frame >= ANIMATION_TIMING.breathingStart) {
    const breathFrame = (frame - ANIMATION_TIMING.breathingStart) % ANIMATION_TIMING.breathingCycleFrames;
    const halfCycle = ANIMATION_TIMING.breathingCycleFrames / 2;
    if (breathFrame <= halfCycle) {
      breathingScale = interpolate(
        breathFrame,
        [0, halfCycle],
        [ANIMATION_TIMING.breathingScaleMin, ANIMATION_TIMING.breathingScaleMax],
        { easing: Easing.inOut(Easing.sin) }
      );
    } else {
      breathingScale = interpolate(
        breathFrame,
        [halfCycle, ANIMATION_TIMING.breathingCycleFrames],
        [ANIMATION_TIMING.breathingScaleMax, ANIMATION_TIMING.breathingScaleMin],
        { easing: Easing.inOut(Easing.sin) }
      );
    }
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
