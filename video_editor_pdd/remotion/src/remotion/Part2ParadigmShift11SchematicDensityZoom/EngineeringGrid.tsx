// ============================================================
// EngineeringGrid.tsx – Faint engineering-paper grid background
// ============================================================
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
  const cols = Math.ceil(width / spacing);
  const rows = Math.ceil(height / spacing);

  return (
    <svg
      width={width}
      height={height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Vertical lines */}
      {Array.from({ length: cols + 1 }, (_, i) => (
        <line
          key={`v${i}`}
          x1={i * spacing}
          y1={0}
          x2={i * spacing}
          y2={height}
          stroke={color}
          strokeWidth={1}
          opacity={opacity}
        />
      ))}
      {/* Horizontal lines */}
      {Array.from({ length: rows + 1 }, (_, i) => (
        <line
          key={`h${i}`}
          x1={0}
          y1={i * spacing}
          x2={width}
          y2={i * spacing}
          stroke={color}
          strokeWidth={1}
          opacity={opacity}
        />
      ))}
    </svg>
  );
};
