import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY } from './constants';

interface PanelLabelProps {
  text: string;
  fadeStart: number;
  fadeEnd: number;
}

export const PanelLabel: React.FC<PanelLabelProps> = ({
  text,
  fadeStart,
  fadeEnd,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [fadeStart, fadeEnd], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: '50%',
        top: 80,
        transform: 'translateX(-50%)',
        fontSize: TYPOGRAPHY.label.fontSize,
        fontFamily: TYPOGRAPHY.label.fontFamily,
        fontWeight: TYPOGRAPHY.label.fontWeight,
        letterSpacing: TYPOGRAPHY.label.letterSpacing,
        color: COLORS.label,
        textTransform: 'uppercase',
        opacity,
      }}
    >
      {text}
    </div>
  );
};
