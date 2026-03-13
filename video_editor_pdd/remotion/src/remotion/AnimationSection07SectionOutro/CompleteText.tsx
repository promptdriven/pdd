import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, DIMENSIONS, TYPOGRAPHY, ANIMATION_TIMING, LABEL_TEXT } from './constants';

export const CompleteText: React.FC = () => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [ANIMATION_TIMING.textFadeStart, ANIMATION_TIMING.textFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const translateY = interpolate(progress, [0, 1], [8, 0]);

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: DIMENSIONS.labelY,
        width: CANVAS.width,
        textAlign: 'center',
        opacity: progress,
        color: COLORS.labelText,
        fontSize: TYPOGRAPHY.label.fontSize,
        fontFamily: TYPOGRAPHY.label.fontFamily,
        fontWeight: TYPOGRAPHY.label.fontWeight,
        letterSpacing: TYPOGRAPHY.label.letterSpacing,
        transform: `translateY(${translateY}px)`,
      }}
    >
      {LABEL_TEXT}
    </div>
  );
};
