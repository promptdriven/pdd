import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { RULE, COLORS, TIMING } from './constants';

/**
 * Animated horizontal rule that draws from center outward.
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
    }
  );

  const currentWidth = RULE.WIDTH * progress;

  return (
    <div
      style={{
        position: 'absolute',
        top: RULE.Y,
        left: '50%',
        transform: 'translateX(-50%)',
        width: currentWidth,
        height: RULE.HEIGHT,
        backgroundColor: COLORS.RULE,
        opacity: RULE.OPACITY,
        borderRadius: 1,
      }}
    />
  );
};
