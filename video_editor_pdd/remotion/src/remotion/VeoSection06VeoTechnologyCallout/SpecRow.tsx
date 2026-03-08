import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, ANIMATION, CARD } from './constants';

interface SpecRowProps {
  label: string;
  value: string;
  index: number;
}

export const SpecRow: React.FC<SpecRowProps> = ({ label, value, index }) => {
  const frame = useCurrentFrame();

  const rowStart = ANIMATION.specsStart + index * ANIMATION.specsStagger;
  const rowEnd = rowStart + 12;

  const opacity = interpolate(
    frame,
    [rowStart, rowEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(3)) },
  );

  const translateX = interpolate(
    frame,
    [rowStart, rowEnd],
    [ANIMATION.specSlideDist, 0],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(3)) },
  );

  const rowWidth = CARD.width - CARD.padding * 2;

  return (
    <div
      style={{
        opacity,
        transform: `translateX(${translateX}px)`,
        display: 'flex',
        flexDirection: 'column',
        gap: 6,
        width: rowWidth,
        marginBottom: 28,
      }}
    >
      <span
        style={{
          color: COLORS.labelText,
          fontSize: TYPOGRAPHY.label.fontSize,
          fontFamily: TYPOGRAPHY.label.fontFamily,
          fontWeight: TYPOGRAPHY.label.fontWeight,
          letterSpacing: TYPOGRAPHY.label.letterSpacing,
          textTransform: TYPOGRAPHY.label.textTransform,
        }}
      >
        {label}
      </span>
      <span
        style={{
          color: COLORS.valueText,
          fontSize: TYPOGRAPHY.value.fontSize,
          fontFamily: TYPOGRAPHY.value.fontFamily,
          fontWeight: TYPOGRAPHY.value.fontWeight,
          letterSpacing: TYPOGRAPHY.value.letterSpacing,
        }}
      >
        {value}
      </span>
      {/* Divider line */}
      <div
        style={{
          width: rowWidth,
          height: 1,
          backgroundColor: COLORS.divider,
          marginTop: 4,
        }}
      />
    </div>
  );
};
