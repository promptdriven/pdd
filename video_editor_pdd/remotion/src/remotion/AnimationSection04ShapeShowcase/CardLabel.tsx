import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, DIMENSIONS, ANIMATION_TIMING } from './constants';

interface CardLabelProps {
  text: string;
  centerX: number;
  cardCenterY: number;
}

export const CardLabel: React.FC<CardLabelProps> = ({
  text,
  centerX,
  cardCenterY,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION_TIMING.labelFadeStart, ANIMATION_TIMING.labelFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  const labelTop = cardCenterY + DIMENSIONS.cardSize / 2 + 24;

  return (
    <div
      style={{
        position: 'absolute',
        top: labelTop,
        left: centerX - DIMENSIONS.cardSize / 2,
        width: DIMENSIONS.cardSize,
        textAlign: 'center',
        opacity,
      }}
    >
      <span
        style={{
          fontFamily: TYPOGRAPHY.label.fontFamily,
          fontSize: TYPOGRAPHY.label.fontSize,
          fontWeight: TYPOGRAPHY.label.fontWeight,
          color: COLORS.labelText,
        }}
      >
        {text}
      </span>
    </div>
  );
};
