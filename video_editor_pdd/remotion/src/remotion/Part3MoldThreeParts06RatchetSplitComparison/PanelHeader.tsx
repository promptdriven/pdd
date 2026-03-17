import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { FONT_SANS } from './constants';

interface PanelHeaderProps {
  text: string;
  color: string;
  centerX: number;
}

export const PanelHeader: React.FC<PanelHeaderProps> = ({ text, color, centerX }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, 20], [0, 0.5], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  return (
    <div
      style={{
        position: 'absolute',
        top: 40,
        left: centerX - 200,
        width: 400,
        textAlign: 'center',
        fontFamily: FONT_SANS,
        fontSize: 14,
        fontWeight: 600,
        color,
        opacity,
        letterSpacing: 2,
      }}
    >
      {text}
    </div>
  );
};
