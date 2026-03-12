import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, type TitleCardLayout } from './constants';

export const HorizontalRule: React.FC<{ layout: TitleCardLayout }> = ({ layout }) => {
  const frame = useCurrentFrame();

  const scaleX = interpolate(
    frame,
    [ANIMATION.ruleFadeStart, ANIMATION.ruleFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        top:
          layout.height / 2 +
          layout.dimensions.titleRuleGap +
          layout.typography.title.fontSize / 2,
        left: layout.width / 2 - layout.dimensions.ruleWidth / 2,
        width: layout.dimensions.ruleWidth,
        height: layout.dimensions.ruleHeight,
        backgroundColor: COLORS.rule,
        transform: `scaleX(${scaleX})`,
        transformOrigin: 'center',
      }}
    />
  );
};
