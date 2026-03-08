import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, TYPOGRAPHY, ANIMATION } from './constants';

export const HeaderTitle: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION.headerFadeStart, ANIMATION.headerFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const translateY = interpolate(
    frame,
    [ANIMATION.headerFadeStart, ANIMATION.headerFadeEnd],
    [-12, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 40,
        width: CANVAS.width,
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'center',
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      <span
        style={{
          color: COLORS.headerText,
          fontFamily: TYPOGRAPHY.header.fontFamily,
          fontWeight: TYPOGRAPHY.header.fontWeight,
          fontSize: TYPOGRAPHY.header.fontSize,
          letterSpacing: '2px',
          textTransform: 'uppercase' as const,
        }}
      >
        Scene Comparison
      </span>
    </div>
  );
};
