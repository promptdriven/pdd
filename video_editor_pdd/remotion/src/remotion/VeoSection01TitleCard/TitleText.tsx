import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, type TitleCardLayout } from './constants';

export const TitleText: React.FC<{ layout: TitleCardLayout }> = ({ layout }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION.titleFadeStart, ANIMATION.titleFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  // Parallax entrance: shifts up 10px as it fades in
  const translateY = interpolate(
    frame,
    [ANIMATION.titleFadeStart, ANIMATION.titleFadeEnd],
    [10, 0],
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
        top: 0,
        left: 0,
        width: layout.width,
        height: layout.height,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
      }}
    >
      <span
        style={{
          fontFamily: layout.typography.title.fontFamily,
          fontSize: layout.typography.title.fontSize,
          fontWeight: layout.typography.title.fontWeight,
          color: COLORS.titleText,
          opacity,
          transform: `translateY(${translateY}px)`,
        }}
      >
        Veo Section
      </span>
    </div>
  );
};
