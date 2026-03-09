import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING } from './constants';

export const ExpandingRule: React.FC = () => {
  const frame = useCurrentFrame();

  const width = interpolate(
    frame,
    [ANIMATION_TIMING.ruleExpandStart, ANIMATION_TIMING.ruleExpandEnd],
    [0, DIMENSIONS.ruleWidth],
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
        left: '50%',
        top: DIMENSIONS.ruleY,
        transform: 'translateX(-50%)',
        width,
        height: DIMENSIONS.ruleHeight,
        backgroundColor: COLORS.accentCyan,
      }}
    />
  );
};
