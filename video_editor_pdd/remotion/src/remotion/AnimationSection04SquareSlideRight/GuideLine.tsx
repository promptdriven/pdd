import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const GuideLine: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in during phase 1
  const fadeInOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.guideFadeInStart, ANIMATION_TIMING.guideFadeInEnd],
    [0, DIMENSIONS.guideLineOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  // Fade out during phase 4
  const fadeOutOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.guideFadeOutStart, ANIMATION_TIMING.guideFadeOutEnd],
    [DIMENSIONS.guideLineOpacity, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.sin),
    }
  );

  const opacity = frame < ANIMATION_TIMING.guideFadeOutStart
    ? fadeInOpacity
    : fadeOutOpacity;

  return (
    <div
      style={{
        position: 'absolute',
        top: DIMENSIONS.centerY,
        left: 0,
        width: CANVAS.width,
        height: 0,
        borderTop: `${DIMENSIONS.guideLineWidth}px dashed ${COLORS.guideLine}`,
        opacity,
      }}
    />
  );
};
