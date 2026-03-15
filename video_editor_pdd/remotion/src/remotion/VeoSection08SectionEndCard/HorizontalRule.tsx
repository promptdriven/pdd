import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, RULE, TIMING } from './constants';

export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();

  // Frames 24-30: Expand from center (0 -> 240px) with easeInOutCubic
  const width = interpolate(
    frame,
    [TIMING.ruleStart, TIMING.ruleEnd],
    [0, RULE.maxWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: RULE.y,
        transform: 'translateX(-50%)',
        width,
        height: RULE.height,
        backgroundColor: COLORS.accent,
        opacity: frame >= TIMING.ruleStart ? 1 : 0,
      }}
    />
  );
};
