import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, DIMENSIONS, ANIMATION, TITLE_TEXT } from './constants';

export const TitleText: React.FC = () => {
  const frame = useCurrentFrame();

  // Frame 8-14: Fade in (opacity 0->1) with easeOutCubic
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

  // Frame 8-14: Slide up from +15px -> 0px
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

  // Frame 22-24: Fade out with all elements
  const fadeOutOpacity = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: DIMENSIONS.titleY,
        width: '100%',
        textAlign: 'center',
        opacity: opacity * fadeOutOpacity,
        transform: `translateY(${translateY}px)`,
        fontFamily: TYPOGRAPHY.title.fontFamily,
        fontSize: TYPOGRAPHY.title.fontSize,
        fontWeight: TYPOGRAPHY.title.fontWeight,
        color: COLORS.titleText,
        lineHeight: 1.2,
      }}
    >
      {TITLE_TEXT}
    </div>
  );
};
