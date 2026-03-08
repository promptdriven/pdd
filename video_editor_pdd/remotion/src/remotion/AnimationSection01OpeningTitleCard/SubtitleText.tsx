import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, TEXT, CANVAS } from './constants';

export const SubtitleText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [0, 15],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: DIMENSIONS.subtitleY,
        width: CANVAS.width,
        textAlign: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: DIMENSIONS.subtitleFontSize,
        fontWeight: 400,
        color: COLORS.subtitleGray,
        letterSpacing: '0.02em',
        lineHeight: 1.5,
        opacity,
      }}
    >
      {TEXT.subtitle}
    </div>
  );
};
