import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, ANIMATION_TIMING, CANVAS } from './constants';

export const ExpandingRule: React.FC = () => {
  const frame = useCurrentFrame();

  const width = interpolate(
    frame,
    [ANIMATION_TIMING.ruleFadeStart, ANIMATION_TIMING.ruleFadeEnd],
    [0, DIMENSIONS.accentLineMaxWidth],
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
        top: CANVAS.height / 2 + 36 + DIMENSIONS.titleToRuleGap,
        transform: 'translateX(-50%)',
        width,
        height: DIMENSIONS.accentLineHeight,
        backgroundColor: COLORS.accentLine,
      }}
    />
  );
};
