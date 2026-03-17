import React from 'react';

interface EngineeringGridProps {
  spacing: number;
  color: string;
  opacity: number;
  width: number;
  height: number;
}

export const EngineeringGrid: React.FC<EngineeringGridProps> = ({
  spacing,
  color,
  opacity,
  width,
  height,
}) => {
  const lines: React.ReactNode[] = [];

  // Vertical lines
  for (let x = 0; x <= width; x += spacing) {
    lines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={height}
        stroke={color}
        strokeWidth={1}
        opacity={opacity}
      />
    );
  }

  // Horizontal lines
  for (let y = 0; y <= height; y += spacing) {
    lines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={width}
        y2={y}
        stroke={color}
        strokeWidth={1}
        opacity={opacity}
      />
    );
  }

  return (
    <svg
      width={width}
      height={height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {lines}
    </svg>
  );
};
