import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CANVAS, COLORS, POSITIONS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const ExpandingRule: React.FC = () => {
  const frame = useCurrentFrame();

  const ruleWidth = interpolate(
    frame,
    [ANIMATION_TIMING.ruleExpandStart, ANIMATION_TIMING.ruleExpandEnd],
    [0, DIMENSIONS.ruleMaxWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  const ruleOpacity = interpolate(
    frame,
    [ANIMATION_TIMING.ruleExpandStart, ANIMATION_TIMING.ruleExpandStart + 6],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.width / 2 - ruleWidth / 2,
        top: POSITIONS.ruleY,
        width: ruleWidth,
        height: DIMENSIONS.ruleHeight,
        background: `linear-gradient(90deg, transparent 0%, ${COLORS.ruleColor} 30%, ${COLORS.ruleColor} 70%, transparent 100%)`,
        opacity: ruleOpacity,
        borderRadius: DIMENSIONS.ruleHeight / 2,
      }}
    />
  );
};
