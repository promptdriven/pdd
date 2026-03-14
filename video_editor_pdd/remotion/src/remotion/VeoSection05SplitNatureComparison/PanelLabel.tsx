import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  COLORS,
  DIMENSIONS,
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
  const isLeft = side === 'left';

  // Left label: frame 14–22, right label: frame 18–26
  const animStart = isLeft ? ANIMATION.leftLabelStart : ANIMATION.rightLabelStart;
  const animEnd = isLeft ? ANIMATION.leftLabelEnd : ANIMATION.rightLabelEnd;

  // Opacity 0→1, easeOutCubic
  const opacity = interpolate(
    frame,
    [animStart, animEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  // TranslateY +10→0, easeOutCubic
  const translateY = interpolate(
    frame,
    [animStart, animEnd],
    [ANIMATION.labelTranslateY, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

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
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      {text}
    </div>
  );
};
