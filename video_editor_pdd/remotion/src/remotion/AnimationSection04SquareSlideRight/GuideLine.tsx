import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, MOTION, TIMING } from './constants';

export const GuideLine: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in during frames 0-3 (0 → 0.15 opacity)
  const fadeInOpacity = interpolate(
    frame,
    [0, TIMING.holdEnd],
    [0, 0.15],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  // Fade out during frames 27-33 (0.15 → 0 opacity)
  const fadeOutOpacity = interpolate(
    frame,
    [TIMING.fadeStart, TIMING.fadeEnd],
    [0.15, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  const opacity =
    frame < TIMING.fadeStart ? fadeInOpacity : fadeOutOpacity;

  return (
    <div
      style={{
        position: 'absolute',
        top: MOTION.centerY,
        left: 0,
        width: CANVAS.width,
        height: 1,
        backgroundColor: `rgba(255, 255, 255, ${opacity})`,
      }}
    />
  );
};
