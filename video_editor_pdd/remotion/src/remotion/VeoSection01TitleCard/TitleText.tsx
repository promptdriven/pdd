import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, type TitleCardLayout } from './constants';

export const TitleText: React.FC<{ layout: TitleCardLayout }> = ({ layout }) => {
  const frame = useCurrentFrame();

  // Frame 0-10: Fade in with easeOutCubic
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

  // Slide up 20px → 0px
  const translateY = interpolate(
    frame,
    [ANIMATION.titleFadeStart, ANIMATION.titleFadeEnd],
    [ANIMATION.titleShiftPx, 0],
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
        top: layout.dimensions.titleY,
        left: 0,
        width: layout.width,
        display: 'flex',
        justifyContent: 'center',
      }}
    >
      <span
        style={{
          fontFamily: layout.typography.title.fontFamily,
          fontSize: layout.typography.title.fontSize,
          fontWeight: layout.typography.title.fontWeight,
          letterSpacing: layout.typography.title.letterSpacing,
          color: COLORS.titleText,
          textTransform: 'uppercase' as const,
          opacity,
          transform: `translateY(${translateY}px)`,
        }}
      >
        VEO SECTION
      </span>
    </div>
  );
};
