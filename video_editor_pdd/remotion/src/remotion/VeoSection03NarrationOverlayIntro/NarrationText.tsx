import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, ANIMATION_TIMING, NARRATION_TEXT } from './constants';

export const NarrationText: React.FC = () => {
  const frame = useCurrentFrame();

  // Text fade in: opacity 0 → 1 (frame 10-20)
  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.textFadeInStart, ANIMATION_TIMING.textFadeInEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <span
      style={{
        fontFamily: TYPOGRAPHY.narration.fontFamily,
        fontSize: TYPOGRAPHY.narration.fontSize,
        fontWeight: TYPOGRAPHY.narration.fontWeight,
        letterSpacing: TYPOGRAPHY.narration.letterSpacing,
        color: COLORS.text,
        textAlign: 'center',
        textShadow: `0 1px 4px ${COLORS.textShadow}`,
        opacity,
      }}
    >
      {NARRATION_TEXT}
    </span>
  );
};
