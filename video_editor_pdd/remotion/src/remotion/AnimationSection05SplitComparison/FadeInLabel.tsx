import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, TYPOGRAPHY, ANIMATION_TIMING } from './constants';

interface FadeInLabelProps {
  text: string;
  x: number;
  fadeStart: number;
}

export const FadeInLabel: React.FC<FadeInLabelProps> = ({ text, x, fadeStart }) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [fadeStart, fadeStart + ANIMATION_TIMING.labelFadeDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const opacity = progress * DIMENSIONS.labelOpacity;
  const translateY = interpolate(progress, [0, 1], [10, 0]);

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: DIMENSIONS.labelY,
        transform: `translateX(-50%) translateY(${translateY}px)`,
        color: COLORS.labelText,
        fontSize: TYPOGRAPHY.label.fontSize,
        fontFamily: TYPOGRAPHY.label.fontFamily,
        fontWeight: TYPOGRAPHY.label.fontWeight,
        textAlign: 'center',
        opacity,
        whiteSpace: 'nowrap',
      }}
    >
      {text}
    </div>
  );
};
