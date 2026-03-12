import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, TYPOGRAPHY, ANIMATION_TIMING } from './constants';

interface FadeInLabelProps {
  text: string;
  x: number;
}

export const FadeInLabel: React.FC<FadeInLabelProps> = ({ text, x }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.labelFadeStart, ANIMATION_TIMING.labelFadeEnd],
    [0, DIMENSIONS.labelOpacity],
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
        left: x,
        top: DIMENSIONS.labelY,
        transform: 'translateX(-50%)',
        color: COLORS.labelText,
        fontSize: TYPOGRAPHY.label.fontSize,
        fontFamily: TYPOGRAPHY.label.fontFamily,
        fontWeight: TYPOGRAPHY.label.fontWeight,
        opacity,
        whiteSpace: 'nowrap',
      }}
    >
      {text}
    </div>
  );
};
