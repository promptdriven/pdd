import React from 'react';
import {
  COLORS,
  DIMENSIONS,
  type SplitNatureComparisonLayout,
} from './constants';

interface HeaderTextProps {
  layout: SplitNatureComparisonLayout;
}

export const HeaderText: React.FC<HeaderTextProps> = ({ layout }) => {
  return (
    <div
      style={{
        position: 'absolute',
        top: DIMENSIONS.headerY * layout.scaleY,
        left: 0,
        width: layout.width,
        textAlign: 'center',
        fontFamily: layout.typography.header.fontFamily,
        fontWeight: layout.typography.header.fontWeight,
        fontSize: layout.typography.header.fontSize,
        letterSpacing: layout.typography.header.letterSpacing,
        color: COLORS.headerText,
      }}
    >
      VEO GENERATION RANGE
    </div>
  );
};
