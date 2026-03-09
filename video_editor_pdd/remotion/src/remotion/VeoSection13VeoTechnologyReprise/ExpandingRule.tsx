import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { LAYOUT, COLORS, ANIMATION } from './constants';

export const ExpandingRule: React.FC = () => {
  const frame = useCurrentFrame();

  const ruleWidth = interpolate(
    frame,
    [ANIMATION.ruleExpandStart, ANIMATION.ruleExpandEnd],
    [0, LAYOUT.ruleWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.poly(2)),
    },
  );

  const fadeOut = interpolate(
    frame,
    [ANIMATION.fadeOutStart, ANIMATION.fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.in(Easing.poly(2)),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: LAYOUT.ruleY,
        left: '50%',
        transform: 'translateX(-50%)',
        width: ruleWidth,
        height: 1,
        backgroundColor: COLORS.rule,
        opacity: fadeOut,
      }}
    />
  );
};
