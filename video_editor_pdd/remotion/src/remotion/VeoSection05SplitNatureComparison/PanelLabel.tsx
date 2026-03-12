import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLORS,
  ANIMATION,
  type SplitNatureComparisonLayout,
} from './constants';

interface PanelLabelProps {
  text: string;
  side: 'left' | 'right';
  layout: SplitNatureComparisonLayout;
}

export const PanelLabel: React.FC<PanelLabelProps> = ({ text, side, layout }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION.labelFadeStart, ANIMATION.labelFadeEnd],
    [0, 0.9],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const x = side === 'left' ? layout.positions.leftLabelX : layout.positions.rightLabelX;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: layout.positions.labelY,
        transform: 'translateX(-50%)',
        fontFamily: layout.typography.label.fontFamily,
        fontWeight: layout.typography.label.fontWeight,
        fontSize: layout.typography.label.fontSize,
        color: COLORS.labelText,
        opacity,
        whiteSpace: 'nowrap',
      }}
    >
      {text}
    </div>
  );
};
