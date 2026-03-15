import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLORS,
  DIMENSIONS,
  ANIMATION,
  type SplitComparisonLayout,
} from './constants';

interface PanelLabelProps {
  text: string;
  side: 'left' | 'right';
  layout: SplitComparisonLayout;
}

export const PanelLabel: React.FC<PanelLabelProps> = ({ text, side, layout }) => {
  const frame = useCurrentFrame();
  const isLeft = side === 'left';

  // Both labels fade in simultaneously: frame 8–10
  const opacity = interpolate(
    frame,
    [ANIMATION.labelFadeStart, ANIMATION.labelFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  // Position label at bottom-left of each respective panel
  const leftPos = isLeft
    ? DIMENSIONS.leftPanelX + DIMENSIONS.labelInsetX
    : DIMENSIONS.rightPanelX + DIMENSIONS.labelInsetX;

  return (
    <div
      style={{
        position: 'absolute',
        left: leftPos * layout.scaleX,
        bottom: DIMENSIONS.labelBottomOffset * layout.scaleY,
        fontFamily: layout.typography.label.fontFamily,
        fontWeight: layout.typography.label.fontWeight,
        fontSize: layout.typography.label.fontSize,
        color: COLORS.labelText,
        whiteSpace: 'nowrap',
        backgroundColor: COLORS.labelBackground,
        padding: `${DIMENSIONS.labelPaddingY * layout.uniformScale}px ${DIMENSIONS.labelPaddingX * layout.uniformScale}px`,
        borderRadius: DIMENSIONS.labelRadius * layout.uniformScale,
        opacity,
      }}
    >
      {text}
    </div>
  );
};
