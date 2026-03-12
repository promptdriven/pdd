import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, CANVAS, ANIMATION, DIMENSIONS } from './constants';

export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();

  const scaleX = interpolate(
    frame,
    [ANIMATION.ruleFadeStart, ANIMATION.ruleFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: CANVAS.height / 2 + DIMENSIONS.titleRuleGap + 32,
        left: CANVAS.width / 2 - DIMENSIONS.ruleWidth / 2,
        width: DIMENSIONS.ruleWidth,
        height: DIMENSIONS.ruleHeight,
        backgroundColor: COLORS.rule,
        transform: `scaleX(${scaleX})`,
        transformOrigin: 'center',
      }}
    />
  );
};
