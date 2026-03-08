import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { POSITIONS, TYPOGRAPHY, COLORS, ANIMATION } from './constants';

export const NarrationLabel: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [
      ANIMATION.backdropFadeStart, ANIMATION.backdropFadeEnd,
      ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd,
    ],
    [0, 1, 1, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: POSITIONS.labelX,
        top: POSITIONS.labelY,
        fontFamily: TYPOGRAPHY.label.fontFamily,
        fontWeight: TYPOGRAPHY.label.fontWeight,
        fontSize: TYPOGRAPHY.label.fontSize,
        letterSpacing: TYPOGRAPHY.label.letterSpacing,
        color: COLORS.labelText,
        textTransform: 'uppercase' as const,
        opacity,
        whiteSpace: 'nowrap',
      }}
    >
      NARRATION SYNC
    </div>
  );
};
