import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, POSITIONS, DIMENSIONS, ANIMATION } from './constants';

export const DividerLine: React.FC = () => {
  const frame = useCurrentFrame();

  const height = interpolate(
    frame,
    [ANIMATION.dividerWipeStart, ANIMATION.dividerWipeEnd],
    [0, DIMENSIONS.videoHeight + 300],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  const glowOpacity = interpolate(
    frame,
    [ANIMATION.dividerWipeStart, ANIMATION.dividerWipeEnd * 0.5, ANIMATION.dividerWipeEnd],
    [0, 0.8, 0.3],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  return (
    <>
      {/* Glow behind divider */}
      <div
        style={{
          position: 'absolute',
          left: POSITIONS.dividerX - 8,
          top: POSITIONS.labelY + 50,
          width: 16,
          height,
          background: `radial-gradient(ellipse at center, ${COLORS.dividerGlow}, transparent)`,
          opacity: glowOpacity,
          zIndex: 9,
        }}
      />
      {/* Main divider line */}
      <div
        style={{
          position: 'absolute',
          left: POSITIONS.dividerX - DIMENSIONS.dividerWidth / 2,
          top: POSITIONS.labelY + 50,
          width: DIMENSIONS.dividerWidth,
          height,
          backgroundColor: COLORS.divider,
          zIndex: 10,
        }}
      />
    </>
  );
};
