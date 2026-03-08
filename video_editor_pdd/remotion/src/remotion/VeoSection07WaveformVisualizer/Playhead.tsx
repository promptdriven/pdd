import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { DIMENSIONS, ANIMATION, COLORS } from './constants';

export const Playhead: React.FC = () => {
  const frame = useCurrentFrame();

  // Linear sweep from left to right
  const progress = interpolate(
    frame,
    [ANIMATION.playheadStart, ANIMATION.playheadEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // Fade out
  const opacity = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [0.8, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.in(Easing.cubic) },
  );

  // Only show after playheadStart
  if (frame < ANIMATION.playheadStart) return null;

  const x = progress * DIMENSIONS.containerWidth;

  return (
    <div
      style={{
        position: 'absolute',
        left: `calc(50% - ${DIMENSIONS.containerWidth / 2}px + ${x}px)`,
        top: `calc(50% - ${DIMENSIONS.containerHeight / 2}px)`,
        width: DIMENSIONS.playheadWidth,
        height: DIMENSIONS.containerHeight,
        backgroundColor: COLORS.playhead,
        opacity,
        zIndex: 10,
      }}
    />
  );
};
