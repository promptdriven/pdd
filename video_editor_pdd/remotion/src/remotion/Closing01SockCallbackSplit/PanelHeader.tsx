import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { TIMING } from './constants';

interface PanelHeaderProps {
  text: string;
  color: string;
  panelX: number;
  panelWidth: number;
}

export const PanelHeader: React.FC<PanelHeaderProps> = ({
  text,
  color,
  panelX,
  panelWidth,
}) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [TIMING.HEADER_FADE_START, TIMING.HEADER_FADE_START + TIMING.HEADER_FADE_DURATION],
    [0, 0.3],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <div
      style={{
        position: 'absolute',
        left: panelX,
        top: 36,
        width: panelWidth,
        textAlign: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize: 12,
        fontWeight: 600,
        color,
        opacity,
        letterSpacing: 3,
        zIndex: 10,
      }}
    >
      {text}
    </div>
  );
};
