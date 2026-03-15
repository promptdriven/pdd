import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, ANIMATION, DIMENSIONS } from './constants';

export const TitleText: React.FC = () => {
  const frame = useCurrentFrame();

  // Frame 0–10: Fade in opacity 0→1, easeOutCubic
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

  // Frame 0–10: Slide up from +20px → 0px
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
        top: `${DIMENSIONS.titleTopPercent * 100}%`,
        left: 0,
        width: '100%',
        display: 'flex',
        justifyContent: 'center',
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      <span
        style={{
          fontFamily: TYPOGRAPHY.title.fontFamily,
          fontSize: TYPOGRAPHY.title.fontSize,
          fontWeight: TYPOGRAPHY.title.fontWeight,
          color: COLORS.titleText,
          lineHeight: 1.2,
          textShadow: `0 2px 8px ${COLORS.titleShadow}`,
        }}
      >
        Veo Section
      </span>
    </div>
  );
};
