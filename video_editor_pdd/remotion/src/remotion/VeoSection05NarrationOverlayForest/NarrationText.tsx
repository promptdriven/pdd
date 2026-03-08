import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLORS,
  TYPOGRAPHY,
  DIMENSIONS,
  ANIMATION_TIMING,
  NARRATION_TEXT,
} from './constants';

export const NarrationText: React.FC = () => {
  const frame = useCurrentFrame();

  // Text reveals left-to-right via clip-path (inset right 100% → 0%)
  const clipReveal = interpolate(
    frame,
    [ANIMATION_TIMING.textRevealStart, ANIMATION_TIMING.textRevealEnd],
    [100, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: DIMENSIONS.accentBarInset + DIMENSIONS.accentBarWidth + 16,
        top: 0,
        height: DIMENSIONS.pillHeight,
        display: 'flex',
        alignItems: 'center',
        clipPath: `inset(0 ${clipReveal}% 0 0)`,
      }}
    >
      <span
        style={{
          fontFamily: TYPOGRAPHY.subtitle.fontFamily,
          fontSize: TYPOGRAPHY.subtitle.fontSize,
          fontWeight: TYPOGRAPHY.subtitle.fontWeight,
          letterSpacing: TYPOGRAPHY.subtitle.letterSpacing,
          color: COLORS.text,
          textShadow: `0 1px 6px ${COLORS.textShadow}`,
          whiteSpace: 'nowrap',
        }}
      >
        {NARRATION_TEXT}
      </span>
    </div>
  );
};
