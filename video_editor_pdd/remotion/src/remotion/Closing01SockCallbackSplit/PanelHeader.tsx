import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { TIMING } from './constants';

/**
 * Converts a hex color string (#RRGGBB) to an rgba() string at the given alpha.
 */
const hexToRgba = (hex: string, alpha: number): string => {
  const r = parseInt(hex.slice(1, 3), 16);
  const g = parseInt(hex.slice(3, 5), 16);
  const b = parseInt(hex.slice(5, 7), 16);
  return `rgba(${r},${g},${b},${alpha})`;
};

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
    [0, 0.6],
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
        color: hexToRgba(color, opacity),
        letterSpacing: 3,
        textShadow: `0 0 8px ${hexToRgba(color, opacity * 0.5)}, 0 1px 4px rgba(0,0,0,${Math.min(opacity * 2, 0.8)})`,
        zIndex: 10,
      }}
    >
      {text}
    </div>
  );
};
