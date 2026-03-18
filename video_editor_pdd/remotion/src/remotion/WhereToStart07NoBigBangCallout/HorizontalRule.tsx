import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TIMING } from './constants';

/**
 * HorizontalRule draws a centered line that expands outward from the center.
 */
export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [TIMING.RULE_START, TIMING.RULE_START + TIMING.RULE_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  const ruleWidth = 160;
  const currentWidth = ruleWidth * progress;
  const centerX = 1920 / 2;

  return (
    <div
      style={{
        position: 'absolute',
        top: 475,
        left: centerX - currentWidth / 2,
        width: currentWidth,
        height: 1.5,
        backgroundColor: COLORS.RULE_COLOR,
        opacity: 0.3,
      }}
    />
  );
};
