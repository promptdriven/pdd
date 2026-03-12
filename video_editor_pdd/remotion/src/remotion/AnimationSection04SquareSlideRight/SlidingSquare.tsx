import React from 'react';
import { useCurrentFrame, interpolate, spring, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

const FPS = 30;

/**
 * The main green square that slides from center to the right.
 * Uses easeInOutCubic for the main slide and spring for the overshoot settle.
 */
export const SlidingSquare: React.FC = () => {
  const frame = useCurrentFrame();

  const { startX, endX, overshootX, squareSize, centerY } = DIMENSIONS;
  const { slideStart, slideEnd, settleStart } = ANIMATION_TIMING;

  // Phase 2: Main slide from startX to overshootX
  const slideX = interpolate(
    frame,
    [slideStart, slideEnd],
    [startX, overshootX],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Phase 3: Spring settle from overshootX back to endX
  const settleProgress = spring({
    frame: Math.max(0, frame - settleStart),
    fps: FPS,
    config: {
      damping: 10,
      stiffness: 160,
    },
  });

  const settleX = interpolate(
    settleProgress,
    [0, 1],
    [overshootX, endX],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' }
  );

  // Combine: use slide position until settle starts, then settle position
  const x = frame < settleStart ? slideX : settleX;

  return (
    <div
      style={{
        position: 'absolute',
        left: x - squareSize / 2,
        top: centerY - squareSize / 2,
        width: squareSize,
        height: squareSize,
        backgroundColor: COLORS.square,
      }}
    />
  );
};
