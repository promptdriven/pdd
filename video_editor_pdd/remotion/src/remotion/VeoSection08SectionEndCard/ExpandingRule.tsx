import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, type EndCardLayout } from './constants';

export const ExpandingRule: React.FC<{ layout: EndCardLayout }> = ({ layout }) => {
  const frame = useCurrentFrame();

  const { ruleWidth, ruleHeight, labelY, ruleGapBelow } = layout.dimensions;

  // Scale outward from centre (scaleX 0 → 1, frames 60-80)
  const scaleX = interpolate(
    frame,
    [ANIMATION.ruleScaleStart, ANIMATION.ruleScaleEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    },
  );

  // Position: 16px below the label
  const ruleTop = labelY + layout.typography.label.fontSize + ruleGapBelow;

  return (
    <div
      style={{
        position: 'absolute',
        left: layout.width / 2 - ruleWidth / 2,
        top: ruleTop,
        width: ruleWidth,
        height: ruleHeight,
        backgroundColor: COLORS.rule,
        borderRadius: ruleHeight / 2,
        transform: `scaleX(${scaleX})`,
        opacity: frame >= ANIMATION.ruleScaleStart ? 1 : 0,
      }}
    />
  );
};
