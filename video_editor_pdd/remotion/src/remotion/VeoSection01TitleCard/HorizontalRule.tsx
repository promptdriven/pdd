import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, ANIMATION, DIMENSIONS } from './constants';

export const HorizontalRule: React.FC = () => {
  const frame = useCurrentFrame();

  // Frame 10–18: Expand width from 0→400px, center-anchored, easeInOutQuad
  const width = interpolate(
    frame,
    [ANIMATION.ruleExpandStart, ANIMATION.ruleExpandEnd],
    [0, DIMENSIONS.ruleMaxWidth],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  // Position: 40% from top + title line-height offset + 20px gap
  // Title is at 40% (432px on 1080p), title fontSize=56, lineHeight=1.2 → ~67px tall
  // Rule sits 20px below the title's bottom edge
  const titleBottomPx = DIMENSIONS.titleTopPercent * 1080 + TYPOGRAPHY.title.fontSize * 1.2;
  const ruleTop = titleBottomPx + DIMENSIONS.ruleGap;

  return (
    <div
      style={{
        position: 'absolute',
        top: ruleTop,
        left: '50%',
        transform: 'translateX(-50%)',
        width,
        height: DIMENSIONS.ruleHeight,
        backgroundColor: COLORS.rule,
      }}
    />
  );
};
