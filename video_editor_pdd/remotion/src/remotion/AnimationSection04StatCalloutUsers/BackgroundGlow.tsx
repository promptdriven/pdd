/**
 * BackgroundGlow component
 * Elliptical gradient glow effect behind the main content
 */

import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { COLORS, POSITIONS, DIMENSIONS } from './constants';

export const BackgroundGlow: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in over first 10 frames
  const opacity = interpolate(
    frame,
    [0, 10],
    [0, 0.15],
    {
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.ease),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: POSITIONS.GLOW.X,
        top: POSITIONS.GLOW.Y,
        width: DIMENSIONS.GLOW_WIDTH,
        height: DIMENSIONS.GLOW_HEIGHT,
        transform: 'translate(-50%, -50%)',
        background: `radial-gradient(ellipse, ${COLORS.GLOW} 0%, transparent 70%)`,
        opacity,
        filter: 'blur(60px)',
      }}
    />
  );
};
