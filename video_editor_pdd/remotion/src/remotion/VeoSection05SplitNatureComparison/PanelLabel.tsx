import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, ANIMATION, DIMENSIONS } from './constants';

interface PanelLabelProps {
  text: string;
  side: 'left' | 'right';
}

export const PanelLabel: React.FC<PanelLabelProps> = ({ text, side }) => {
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

  const x = side === 'left' ? DIMENSIONS.leftLabelX : DIMENSIONS.rightLabelX;

  return (
    <div
      style={{
        position: 'absolute',
        left: x,
        top: DIMENSIONS.labelY,
        transform: 'translateX(-50%)',
        fontFamily: TYPOGRAPHY.label.fontFamily,
        fontWeight: TYPOGRAPHY.label.fontWeight,
        fontSize: TYPOGRAPHY.label.fontSize,
        color: COLORS.labelText,
        opacity,
        whiteSpace: 'nowrap',
      }}
    >
      {text}
    </div>
  );
};
