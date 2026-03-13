import React from 'react';
import {
  COLORS,
  DIMENSIONS,
  type SplitNatureComparisonLayout,
} from './constants';

export const VerticalDivider: React.FC<{ layout: SplitNatureComparisonLayout }> = ({
  layout,
}) => {
  const scaledWidth = Math.max(2, DIMENSIONS.dividerWidth * layout.scaleX);
  const scaledHeight = DIMENSIONS.dividerHeight * layout.scaleY;
  const scaledTop = DIMENSIONS.dividerY * layout.scaleY;
  const scaledLeft = DIMENSIONS.dividerX * layout.scaleX - scaledWidth / 2;
  const glowRadius = DIMENSIONS.dividerGlowRadius * layout.uniformScale;

  return (
    <div
      style={{
        position: 'absolute',
        left: scaledLeft,
        top: scaledTop,
        width: scaledWidth,
        height: scaledHeight,
        backgroundColor: COLORS.divider,
        boxShadow: `0 0 ${glowRadius}px ${COLORS.dividerGlow}`,
      }}
    />
  );
};
