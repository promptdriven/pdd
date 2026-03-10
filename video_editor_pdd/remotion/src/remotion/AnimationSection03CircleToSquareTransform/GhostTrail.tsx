import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { DIMENSIONS, COLORS, GHOST_TRAIL, ANIMATION_TIMING } from './constants';

export const GhostTrail: React.FC = () => {
  const frame = useCurrentFrame();

  // Only render during slide and settle phases
  if (frame < ANIMATION_TIMING.slideStart || frame >= ANIMATION_TIMING.finalHoldStart) {
    return null;
  }

  return (
    <>
      {GHOST_TRAIL.opacities.map((opacity, i) => {
        // Each ghost echo is delayed by (i+1) * frameDelay
        const delayedFrame = frame - (i + 1) * GHOST_TRAIL.frameDelay;

        const ghostX = interpolate(
          delayedFrame,
          [ANIMATION_TIMING.slideStart, ANIMATION_TIMING.slideEnd],
          [DIMENSIONS.centerX, DIMENSIONS.finalX],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.cubic),
          }
        );

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              width: DIMENSIONS.shapeSize,
              height: DIMENSIONS.shapeSize,
              backgroundColor: COLORS.squareYellow,
              borderRadius: '0%',
              opacity,
              left: ghostX - DIMENSIONS.shapeSize / 2,
              top: DIMENSIONS.centerY - DIMENSIONS.shapeSize / 2,
            }}
          />
        );
      })}
    </>
  );
};
