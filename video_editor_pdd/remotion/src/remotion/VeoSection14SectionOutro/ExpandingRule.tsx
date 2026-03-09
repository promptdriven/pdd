import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, POSITIONS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const ExpandingRule: React.FC = () => {
  const frame = useCurrentFrame();

  const width = interpolate(
    frame,
    [ANIMATION_TIMING.ruleStart, ANIMATION_TIMING.ruleEnd],
    [0, DIMENSIONS.ruleWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  if (width <= 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        top: POSITIONS.ruleY,
        left: (CANVAS.width - width) / 2,
        width,
        height: DIMENSIONS.ruleHeight,
        backgroundColor: COLORS.horizontalRule,
      }}
    />
  );
};
