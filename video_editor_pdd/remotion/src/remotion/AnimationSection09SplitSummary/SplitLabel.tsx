import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { LABEL, TYPOGRAPHY, COLORS, TIMING } from './constants';

export const SplitLabel: React.FC = () => {
  const frame = useCurrentFrame();

  // Label fades in during frames 18-22, easeOutQuad
  const labelOpacity = interpolate(
    frame,
    [TIMING.labelFadeStart, TIMING.labelFadeEnd],
    [0, COLORS.labelOpacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  return (
    <div
      style={{
        position: 'absolute',
        top: LABEL.y,
        left: LABEL.x,
        fontSize: TYPOGRAPHY.label.fontSize,
        fontWeight: TYPOGRAPHY.label.fontWeight,
        fontFamily: TYPOGRAPHY.label.fontFamily,
        color: COLORS.labelColor,
        opacity: labelOpacity,
      }}
    >
      {LABEL.text}
    </div>
  );
};
