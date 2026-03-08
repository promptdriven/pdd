import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, DIMENSIONS, TEXT, CANVAS } from './constants';

export const TitleText: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [0, 15],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.poly(4),
    }
  );

  const scale = interpolate(
    frame,
    [0, 15],
    [0.8, 1.0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.poly(4),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: DIMENSIONS.titleY,
        width: CANVAS.width,
        textAlign: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: DIMENSIONS.titleFontSize,
        fontWeight: 700,
        color: COLORS.titleWhite,
        letterSpacing: '0.05em',
        textTransform: 'uppercase',
        lineHeight: 1.2,
        opacity,
        transform: `scale(${scale})`,
      }}
    >
      {TEXT.title}
    </div>
  );
};
