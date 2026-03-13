import React from 'react';
import { useCurrentFrame, interpolate, spring, Easing } from 'remotion';
import { COLORS, SQUARE, MOTION, TIMING, FPS } from './constants';

/**
 * The main green square that slides from center to the right.
 * Uses easeOutCubic for the main slide and spring for the overshoot settle.
 */
export const SlidingSquare: React.FC = () => {
  const frame = useCurrentFrame();

  // Phase 2: Main slide from startX to overshootX (frames 3-22)
  const slideX = interpolate(
    frame,
    [TIMING.slideStart, TIMING.slideEnd],
    [MOTION.startX, MOTION.overshootX],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  // Phase 3: Spring settle from overshootX back to targetX (frames 22-27)
  const settleProgress = spring({
    frame: Math.max(0, frame - TIMING.settleStart),
    fps: FPS,
    config: {
      damping: 16,
      stiffness: 220,
      mass: 1,
    },
  });

  const settleX = interpolate(
    settleProgress,
    [0, 1],
    [MOTION.overshootX, MOTION.targetX],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // Use slide position until settle starts, then settle position
  const x = frame < TIMING.settleStart ? slideX : settleX;

  return (
    <div
      style={{
        position: 'absolute',
        left: x - SQUARE.size / 2,
        top: MOTION.centerY - SQUARE.size / 2,
        width: SQUARE.size,
        height: SQUARE.size,
        backgroundColor: COLORS.square,
        borderRadius: SQUARE.borderRadius,
      }}
    />
  );
};
