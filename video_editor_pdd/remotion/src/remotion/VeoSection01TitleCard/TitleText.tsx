import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, POSITIONS, ANIMATION_TIMING } from './constants';

export const TitleText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.titleFadeStart, ANIMATION_TIMING.titleFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const translateY = interpolate(
    frame,
    [ANIMATION_TIMING.titleFadeStart, ANIMATION_TIMING.titleFadeEnd],
    [-25, 0],
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
        top: POSITIONS.titleY,
        left: 0,
        right: 0,
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
          letterSpacing: TYPOGRAPHY.title.letterSpacing,
          color: COLORS.titleText,
          textAlign: 'center',
        }}
      >
        Veo Section
      </span>
    </div>
  );
};
