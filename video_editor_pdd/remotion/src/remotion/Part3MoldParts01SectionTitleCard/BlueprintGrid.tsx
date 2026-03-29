import React from 'react';
import { AbsoluteFill } from 'remotion';

interface BlueprintGridProps {
  spacing: number;
  color: string;
  opacity: number;
  width: number;
  height: number;
}

export const BlueprintGrid: React.FC<BlueprintGridProps> = ({
  spacing,
  color,
  opacity,
  width,
  height,
}) => {
  const verticalLines: React.ReactNode[] = [];
  const horizontalLines: React.ReactNode[] = [];

  for (let x = 0; x <= width; x += spacing) {
    verticalLines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={height}
        stroke={color}
        strokeWidth={1}
      />
    );
  }

  for (let y = 0; y <= height; y += spacing) {
    horizontalLines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={width}
        y2={y}
        stroke={color}
        strokeWidth={1}
      />
    );
  }

  return (
    <AbsoluteFill>
      <svg
        width={width}
        height={height}
        style={{ opacity, position: 'absolute', top: 0, left: 0 }}
      >
        {verticalLines}
        {horizontalLines}
      </svg>
    </AbsoluteFill>
  );
};
