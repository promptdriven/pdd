import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION } from './constants';

export const ExpandingRule: React.FC = () => {
  const frame = useCurrentFrame();

  // Expand from center (scaleX 0 → 1, frames 16-22) with easeInOutQuad
  const scaleX = interpolate(
    frame,
    [ANIMATION.textFadeStart, ANIMATION.textFadeEnd],
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
        left: (1920 - DIMENSIONS.ruleWidth) / 2,
        top: DIMENSIONS.ruleY,
        width: DIMENSIONS.ruleWidth,
        height: DIMENSIONS.ruleHeight,
        backgroundColor: COLORS.accent,
        borderRadius: DIMENSIONS.ruleHeight / 2,
        transform: `scaleX(${scaleX})`,
        transformOrigin: 'center',
        opacity: frame >= ANIMATION.textFadeStart ? 1 : 0,
      }}
    />
  );
};
