import React from 'react';

interface PanelHeaderProps {
  text: string;
  color: string;
  opacity: number;
  letterSpacing: number;
  y: number;
  fontSize: number;
  fontWeight: number;
  panelWidth: number;
}

export const PanelHeader: React.FC<PanelHeaderProps> = ({
  text,
  color,
  opacity,
  letterSpacing,
  y,
  fontSize,
  fontWeight,
  panelWidth,
}) => {
  return (
    <div
      style={{
        position: 'absolute',
        top: y,
        left: 0,
        width: panelWidth,
        textAlign: 'center',
        fontFamily: 'Inter, sans-serif',
        fontSize,
        fontWeight,
        letterSpacing,
        color,
        opacity,
        zIndex: 10,
        userSelect: 'none',
      }}
    >
      {text}
    </div>
  );
};
