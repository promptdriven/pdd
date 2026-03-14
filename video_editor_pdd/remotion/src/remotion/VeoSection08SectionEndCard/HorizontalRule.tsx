import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION } from './constants';

export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();

  // Frame 14-18: Expand from center (width 0->300px) with easeInOutQuad
  const width = interpolate(
    frame,
    [ANIMATION.ruleExpandStart, ANIMATION.ruleExpandEnd],
    [0, DIMENSIONS.ruleMaxWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  // Frame 22-24: Fade out with all elements
  const fadeOutOpacity = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: DIMENSIONS.ruleY,
        transform: 'translateX(-50%)',
        width,
        height: DIMENSIONS.ruleHeight,
        backgroundColor: COLORS.rule,
        opacity: frame >= ANIMATION.ruleExpandStart ? fadeOutOpacity : 0,
      }}
    />
  );
};
