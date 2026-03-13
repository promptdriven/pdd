import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, SQUARE, MOTION, TRAILS, TIMING } from './constants';

/**
 * Calculates the main square X position at a given frame.
 */
const getSquareX = (f: number): number => {
  if (f <= TIMING.slideStart) return MOTION.startX;
  if (f <= TIMING.slideEnd) {
    return interpolate(
      f,
      [TIMING.slideStart, TIMING.slideEnd],
      [MOTION.startX, MOTION.overshootX],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.cubic),
      },
    );
  }
  return MOTION.overshootX;
};

/**
 * Renders 4 ghost copies of the square trailing behind the main square.
 * Each ghost is delayed by a fixed number of frames and has decreasing opacity.
 */
export const MotionTrail: React.FC = () => {
  const frame = useCurrentFrame();

  // Trail ghosts fade out after the slide completes (during settle phase)
  const trailFadeOut = interpolate(
    frame,
    [TIMING.settleStart, TIMING.settleEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  // Only show trail once the slide starts
  if (frame < TIMING.slideStart) return null;

  return (
    <>
      {TRAILS.map((trail, i) => {
        // Each ghost uses the square position from `delay` frames ago
        const delayedFrame = Math.max(TIMING.slideStart, frame - trail.delay);
        const ghostX = getSquareX(delayedFrame);
        const opacity = trail.opacity * trailFadeOut;

        if (opacity <= 0) return null;

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: ghostX - SQUARE.size / 2,
              top: MOTION.centerY - SQUARE.size / 2,
              width: SQUARE.size,
              height: SQUARE.size,
              backgroundColor: COLORS.square,
              borderRadius: SQUARE.borderRadius,
              opacity,
            }}
          />
        );
      })}
    </>
  );
};
