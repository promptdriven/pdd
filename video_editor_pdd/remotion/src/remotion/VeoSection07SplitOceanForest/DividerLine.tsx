import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, DIMENSIONS, ANIMATION } from './constants';

export const DividerLine: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION.dividerFadeStart, ANIMATION.dividerFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <>
      {/* Soft amber glow behind divider */}
      <div
        style={{
          position: 'absolute',
          left: CANVAS.dividerX - DIMENSIONS.dividerGlowWidth / 2,
          top: 0,
          width: DIMENSIONS.dividerGlowWidth,
          height: CANVAS.height,
          background: COLORS.dividerGlow,
          filter: 'blur(8px)',
          opacity,
          zIndex: 9,
        }}
      />
      {/* Main divider line */}
      <div
        style={{
          position: 'absolute',
          left: CANVAS.dividerX - DIMENSIONS.dividerWidth / 2,
          top: 0,
          width: DIMENSIONS.dividerWidth,
          height: CANVAS.height,
          backgroundColor: COLORS.divider,
          opacity,
          zIndex: 10,
        }}
      />
    </>
  );
};
