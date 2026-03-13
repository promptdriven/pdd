import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, DIMENSIONS, ANIMATION, TAGLINE_TEXT } from './constants';

export const TaglineText: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in (opacity 0 → 0.7, frames 22-28) with easeOutCubic
  const opacity = interpolate(
    frame,
    [ANIMATION.taglineFadeStart, ANIMATION.taglineFadeEnd],
    [0, 0.7],
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
        top: DIMENSIONS.taglineY,
        width: '100%',
        textAlign: 'center',
        opacity,
        fontFamily: TYPOGRAPHY.tagline.fontFamily,
        fontSize: TYPOGRAPHY.tagline.fontSize,
        fontWeight: TYPOGRAPHY.tagline.fontWeight,
        letterSpacing: TYPOGRAPHY.tagline.letterSpacing,
        color: COLORS.taglineText,
      }}
    >
      {TAGLINE_TEXT}
    </div>
  );
};
