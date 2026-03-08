import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, POSITIONS, ANIMATION_TIMING, DIMENSIONS } from './constants';

export const TitleText: React.FC = () => {
  const frame = useCurrentFrame();

  const y = interpolate(
    frame,
    [ANIMATION_TIMING.titleSlideStart, ANIMATION_TIMING.titleSlideEnd],
    [POSITIONS.titleStartY, POSITIONS.titleY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.titleSlideStart, ANIMATION_TIMING.titleSlideEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        right: 0,
        top: y,
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'center',
        opacity,
      }}
    >
      <h1
        style={{
          fontFamily: TYPOGRAPHY.title.fontFamily,
          fontSize: TYPOGRAPHY.title.fontSize,
          fontWeight: TYPOGRAPHY.title.fontWeight,
          letterSpacing: TYPOGRAPHY.title.letterSpacing,
          color: COLORS.titleText,
          margin: 0,
          textShadow: `0 0 ${DIMENSIONS.glowBlurRadius}px rgba(59, 130, 246, 0.5)`,
        }}
      >
        Animation Section
      </h1>
    </div>
  );
};
