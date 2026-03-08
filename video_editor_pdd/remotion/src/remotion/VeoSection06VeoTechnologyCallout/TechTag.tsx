import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, ANIMATION } from './constants';

interface TechTagProps {
  label: string;
  index: number;
}

export const TechTag: React.FC<TechTagProps> = ({ label, index }) => {
  const frame = useCurrentFrame();

  const tagStart = ANIMATION.tagsStart + index * ANIMATION.tagsStagger;
  const tagEnd = tagStart + 10;

  const opacity = interpolate(
    frame,
    [tagStart, tagEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(2)) },
  );

  const scale = interpolate(
    frame,
    [tagStart, tagEnd],
    [0.7, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.poly(3)) },
  );

  return (
    <div
      style={{
        opacity,
        transform: `scale(${scale})`,
        padding: '6px 14px',
        borderRadius: 8,
        backgroundColor: COLORS.tagBg,
        border: `1px solid ${COLORS.tagBorder}`,
        display: 'inline-flex',
        alignItems: 'center',
      }}
    >
      <span
        style={{
          color: COLORS.tagText,
          fontSize: TYPOGRAPHY.tag.fontSize,
          fontFamily: TYPOGRAPHY.tag.fontFamily,
          fontWeight: TYPOGRAPHY.tag.fontWeight,
          letterSpacing: TYPOGRAPHY.tag.letterSpacing,
          whiteSpace: 'nowrap',
        }}
      >
        {label}
      </span>
    </div>
  );
};
