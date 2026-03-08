import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, POSITIONS, ANIMATION_TIMING, CANVAS } from './constants';

export const ExpandingRule: React.FC = () => {
  const frame = useCurrentFrame();

  const width = interpolate(
    frame,
    [ANIMATION_TIMING.ruleExpandStart, ANIMATION_TIMING.ruleExpandEnd],
    [0, DIMENSIONS.ruleMaxWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: CANVAS.width / 2 - width / 2,
        top: POSITIONS.ruleY,
        width,
        height: DIMENSIONS.ruleHeight,
        backgroundColor: COLORS.rule,
        boxShadow: `0 0 12px ${COLORS.rule}`,
      }}
    />
  );
};
