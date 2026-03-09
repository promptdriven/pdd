import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, POSITIONS, ANIMATION, WORDMARK_TEXT } from './constants';

export const VeoWordmark: React.FC = () => {
  const frame = useCurrentFrame();

  // Scale in: frames 10-30, easeOutBack
  const scale = interpolate(
    frame,
    [ANIMATION.wordmarkStart, ANIMATION.wordmarkEnd],
    [ANIMATION.wordmarkScaleFrom, ANIMATION.wordmarkScaleTo],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.7)),
    },
  );

  // Opacity in: frames 10-30
  const opacityIn = interpolate(
    frame,
    [ANIMATION.wordmarkStart, ANIMATION.wordmarkEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  // Fade out: frames 75-90
  const opacityOut = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.poly(2)),
    },
  );

  const opacity = Math.min(opacityIn, opacityOut);

  return (
    <div
      style={{
        position: 'absolute',
        top: POSITIONS.wordmarkY - TYPOGRAPHY.wordmark.fontSize / 2,
        left: 0,
        width: '100%',
        display: 'flex',
        justifyContent: 'center',
        alignItems: 'center',
        opacity,
        transform: `scale(${scale})`,
        transformOrigin: 'center center',
      }}
    >
      <span
        style={{
          color: COLORS.wordmark,
          fontSize: TYPOGRAPHY.wordmark.fontSize,
          fontFamily: TYPOGRAPHY.wordmark.fontFamily,
          fontWeight: TYPOGRAPHY.wordmark.fontWeight,
          letterSpacing: TYPOGRAPHY.wordmark.letterSpacing,
          lineHeight: 1,
        }}
      >
        {WORDMARK_TEXT}
      </span>
    </div>
  );
};
