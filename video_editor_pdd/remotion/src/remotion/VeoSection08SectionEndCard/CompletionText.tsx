import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, DIMENSIONS, ANIMATION, COMPLETION_TEXT } from './constants';

export const CompletionText: React.FC = () => {
  const frame = useCurrentFrame();

  // Fade in + slide up 15px (frames 16-22) with easeOutCubic
  const opacity = interpolate(
    frame,
    [ANIMATION.textFadeStart, ANIMATION.textFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const translateY = interpolate(
    frame,
    [ANIMATION.textFadeStart, ANIMATION.textFadeEnd],
    [ANIMATION.textSlideY, 0],
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
        top: DIMENSIONS.completionTextY,
        width: '100%',
        textAlign: 'center',
        opacity,
        transform: `translateY(${translateY}px)`,
        fontFamily: TYPOGRAPHY.completion.fontFamily,
        fontSize: TYPOGRAPHY.completion.fontSize,
        fontWeight: TYPOGRAPHY.completion.fontWeight,
        letterSpacing: TYPOGRAPHY.completion.letterSpacing,
        color: COLORS.completionText,
      }}
    >
      {COMPLETION_TEXT}
    </div>
  );
};
