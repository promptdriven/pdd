import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, ANIMATION_TIMING, LABEL_TEXT } from './constants';

export const CompleteText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.textFadeStart, ANIMATION_TIMING.textFadeEnd],
    [0, 0.8],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const translateY = interpolate(
    frame,
    [ANIMATION_TIMING.textFadeStart, ANIMATION_TIMING.textFadeEnd],
    [3, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: 400,
        transform: `translate(-50%, -50%) translateY(${translateY}px)`,
        opacity,
        color: COLORS.labelText,
        fontSize: TYPOGRAPHY.label.fontSize,
        fontFamily: TYPOGRAPHY.label.fontFamily,
        fontWeight: TYPOGRAPHY.label.fontWeight,
      }}
    >
      {LABEL_TEXT}
    </div>
  );
};
