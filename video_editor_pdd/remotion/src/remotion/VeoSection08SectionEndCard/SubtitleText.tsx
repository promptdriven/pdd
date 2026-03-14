import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, DIMENSIONS, ANIMATION, SUBTITLE_TEXT } from './constants';

export const SubtitleText: React.FC = () => {
  const frame = useCurrentFrame();

  // Frame 18-22: Fade in (opacity 0->1) with easeOutCubic
  const opacity = interpolate(
    frame,
    [ANIMATION.subtitleFadeStart, ANIMATION.subtitleFadeEnd],
    [0, 1],
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
        top: DIMENSIONS.subtitleY,
        width: '100%',
        textAlign: 'center',
        opacity: opacity * fadeOutOpacity,
        fontFamily: TYPOGRAPHY.subtitle.fontFamily,
        fontSize: TYPOGRAPHY.subtitle.fontSize,
        fontWeight: TYPOGRAPHY.subtitle.fontWeight,
        color: COLORS.subtitleText,
      }}
    >
      {SUBTITLE_TEXT}
    </div>
  );
};
