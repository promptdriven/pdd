import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

/**
 * Renders ghost copies of the square that trail behind the main square.
 * Each ghost is delayed by a fixed number of frames and has decreasing opacity.
 */
export const MotionTrail: React.FC = () => {
  const frame = useCurrentFrame();

  const { trailCount, trailOpacities, trailSpacing, trailDelayFrames } = DIMENSIONS;
  const { slideStart, slideEnd, settleEnd } = ANIMATION_TIMING;

  // Calculate main square X position at a given frame
  const getSquareX = (f: number): number => {
    if (f <= slideStart) return DIMENSIONS.startX;
    if (f <= slideEnd) {
      return interpolate(
        f,
        [slideStart, slideEnd],
        [DIMENSIONS.startX, DIMENSIONS.endX],
        {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
          easing: Easing.inOut(Easing.cubic),
        }
      );
    }
    // After slide, square is at endX (overshoot handled in main component)
    return DIMENSIONS.endX;
  };

  // Trail ghosts fade out after the slide ends
  const trailFadeOut = interpolate(
    frame,
    [slideEnd, settleEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Only show trail during and after the slide
  if (frame < slideStart) return null;

  return (
    <>
      {Array.from({ length: trailCount }).map((_, i) => {
        const ghostIndex = i + 1;
        const delayedFrame = Math.max(slideStart, frame - ghostIndex * trailDelayFrames);
        const ghostX = getSquareX(delayedFrame);
        const baseOpacity = trailOpacities[i] ?? 0.03;
        const opacity = baseOpacity * trailFadeOut;

        // Only render if the ghost is actually behind the square
        const mainX = getSquareX(frame);
        if (ghostX >= mainX && frame > slideStart + ghostIndex * trailDelayFrames) return null;

        return (
          <div
            key={i}
            style={{
              position: 'absolute',
              left: ghostX - DIMENSIONS.squareSize / 2,
              top: DIMENSIONS.centerY - DIMENSIONS.squareSize / 2,
              width: DIMENSIONS.squareSize,
              height: DIMENSIONS.squareSize,
              backgroundColor: COLORS.square,
              opacity,
            }}
          />
        );
      })}
    </>
  );
};
