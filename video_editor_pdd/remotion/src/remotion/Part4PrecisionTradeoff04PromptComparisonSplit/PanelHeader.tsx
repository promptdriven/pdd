import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

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

  const opacity = interpolate(frame, [0, 20], [0, 0.5], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.cubic),
  });

  return (
    <div
      style={{
        position: 'absolute',
        left: panelX,
        top: 8,
        width: panelWidth,
        height: 30,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        opacity,
      }}
    >
      <span
        style={{
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          fontWeight: 600,
          color,
          letterSpacing: 2,
        }}
      >
        {text}
      </span>
    </div>
  );
};
