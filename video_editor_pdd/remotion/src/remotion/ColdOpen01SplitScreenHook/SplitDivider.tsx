import React from 'react';

interface SplitDividerProps {
  x: number;
  width: number;
  color: string;
  opacity: number;
  canvasHeight: number;
}

export const SplitDivider: React.FC<SplitDividerProps> = ({
  x,
  width,
  color,
  opacity,
  canvasHeight,
}) => {
  return (
    <div
      style={{
        position: 'absolute',
        left: x - width / 2,
        top: 0,
        width,
        height: canvasHeight,
        backgroundColor: color,
        opacity,
      }}
    />
  );
};
