import React from 'react';
import {
  COLORS,
  DIMENSIONS,
  type SplitNatureComparisonLayout,
} from './constants';

interface PanelLabelProps {
  text: string;
  side: 'left' | 'right';
  layout: SplitNatureComparisonLayout;
}

export const PanelLabel: React.FC<PanelLabelProps> = ({ text, side, layout }) => {
  const isLeft = side === 'left';
  const centerX = isLeft
    ? DIMENSIONS.leftLabelCenterX * layout.scaleX
    : DIMENSIONS.rightLabelCenterX * layout.scaleX;
  const color = isLeft ? COLORS.leftLabel : COLORS.rightLabel;

  return (
    <div
      style={{
        position: 'absolute',
        left: centerX,
        top: DIMENSIONS.labelY * layout.scaleY,
        transform: 'translateX(-50%)',
        fontFamily: layout.typography.label.fontFamily,
        fontWeight: layout.typography.label.fontWeight,
        fontSize: layout.typography.label.fontSize,
        color,
        whiteSpace: 'nowrap',
      }}
    >
      {text}
    </div>
  );
};
