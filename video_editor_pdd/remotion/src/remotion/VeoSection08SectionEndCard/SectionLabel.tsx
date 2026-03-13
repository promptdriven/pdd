import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, LABEL_TEXT, type EndCardLayout } from './constants';

export const SectionLabel: React.FC<{ layout: EndCardLayout }> = ({ layout }) => {
  const frame = useCurrentFrame();

  // Fade in with translateY drift (frames 50-70)
  const opacity = interpolate(
    frame,
    [ANIMATION.labelFadeStart, ANIMATION.labelFadeEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const translateY = interpolate(
    frame,
    [ANIMATION.labelFadeStart, ANIMATION.labelFadeEnd],
    [ANIMATION.labelShiftPx * layout.uniformScale, 0],
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
        left: 0,
        top: layout.dimensions.labelY,
        width: layout.width,
        textAlign: 'center',
        opacity,
        transform: `translateY(${translateY}px)`,
        fontFamily: layout.typography.label.fontFamily,
        fontSize: layout.typography.label.fontSize,
        fontWeight: layout.typography.label.fontWeight,
        color: COLORS.labelText,
      }}
    >
      {LABEL_TEXT}
    </div>
  );
};
