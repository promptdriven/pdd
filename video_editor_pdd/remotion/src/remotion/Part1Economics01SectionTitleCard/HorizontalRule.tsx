import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import { COLORS, TIMING, LAYOUT } from './constants';

export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [0, TIMING.RULE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const currentWidth = LAYOUT.ruleTotalWidth * progress;

  return (
    <div
      style={{
        position: 'absolute',
        top: LAYOUT.ruleY,
        left: LAYOUT.centerX - currentWidth / 2,
        width: currentWidth,
        height: LAYOUT.ruleThickness,
        backgroundColor: COLORS.amber,
        opacity: 0.2,
      }}
    />
  );
};

export default HorizontalRule;
