import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, ANIMATION } from './constants';

interface SplitLabelProps {
  text: string;
  x: number;
  y: number;
  align: 'left' | 'right';
}

export const SplitLabel: React.FC<SplitLabelProps> = ({
  text,
  x,
  y,
  align,
}) => {
  const frame = useCurrentFrame();

  // Fade in with upward drift (frames 20-30)
  const fadeInOpacity = interpolate(
    frame,
    [ANIMATION.labelFadeInStart, ANIMATION.labelFadeInEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const driftY = interpolate(
    frame,
    [ANIMATION.labelFadeInStart, ANIMATION.labelFadeInEnd],
    [12, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // Fade out (frames 75-90)
  const fadeOutOpacity = interpolate(
    frame,
    [ANIMATION.labelFadeOutStart, ANIMATION.labelFadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const opacity = fadeInOpacity * fadeOutOpacity;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: y,
        transform: `translateY(${driftY}px)`,
        fontSize: TYPOGRAPHY.label.fontSize,
        fontFamily: TYPOGRAPHY.label.fontFamily,
        fontWeight: TYPOGRAPHY.label.fontWeight,
        letterSpacing: TYPOGRAPHY.label.letterSpacing,
        color: COLORS.label,
        textTransform: 'uppercase',
        textAlign: align,
        opacity,
        zIndex: 11,
      }}
    >
      {text}
    </div>
  );
};
