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

  return (
    <div
      style={{
        position: 'absolute',
        [isLeft ? 'left' : 'right']: DIMENSIONS.labelInsetX * layout.scaleX,
        bottom: DIMENSIONS.labelBottomOffset * layout.scaleY,
        fontFamily: layout.typography.label.fontFamily,
        fontWeight: layout.typography.label.fontWeight,
        fontSize: layout.typography.label.fontSize,
        color: COLORS.labelText,
        whiteSpace: 'nowrap',
        backgroundColor: COLORS.labelBackground,
        padding: `${DIMENSIONS.labelPaddingY * layout.uniformScale}px ${DIMENSIONS.labelPaddingX * layout.uniformScale}px`,
        borderRadius: DIMENSIONS.labelRadius * layout.uniformScale,
        textAlign: isLeft ? 'left' : 'right',
      }}
    >
      {text}
    </div>
  );
};
