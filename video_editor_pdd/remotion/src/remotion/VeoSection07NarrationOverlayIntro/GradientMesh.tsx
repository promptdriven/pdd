import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION } from './constants';

export const GradientMesh: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in over the first 6 frames — start at 0.6 so content is visible from frame 0
  const opacity = interpolate(
    frame,
    [ANIMATION.meshFadeStart, ANIMATION.meshFadeEnd],
    [0.6, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Slow-cycling gradient angle for mesh movement
  const angle = 135 + frame * 0.8;
  const [c1, c2, c3] = COLORS.gradientMesh;

  return (
    <div
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: '100%',
        height: '100%',
        background: `
          linear-gradient(${angle}deg, ${c1} 0%, ${c2} 50%, ${c3} 100%)
        `,
        opacity,
      }}
    />
  );
};
