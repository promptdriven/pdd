import React from 'react';
import { AbsoluteFill } from 'remotion';

interface BlueprintGridProps {
  spacing: number;
  color: string;
  opacity: number;
  canvasWidth: number;
  canvasHeight: number;
}

export const BlueprintGrid: React.FC<BlueprintGridProps> = ({
  spacing,
  color,
  opacity,
  canvasWidth,
  canvasHeight,
}) => {
  const verticalLines: React.ReactNode[] = [];
  const horizontalLines: React.ReactNode[] = [];

  for (let x = 0; x <= canvasWidth; x += spacing) {
    verticalLines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={canvasHeight}
        stroke={color}
        strokeWidth={1}
        opacity={opacity}
      />
    );
  }

  for (let y = 0; y <= canvasHeight; y += spacing) {
    horizontalLines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={canvasWidth}
        y2={y}
        stroke={color}
        strokeWidth={1}
        opacity={opacity}
      />
    );
  }

  return (
    <AbsoluteFill>
      <svg width={canvasWidth} height={canvasHeight}>
        {verticalLines}
        {horizontalLines}
      </svg>
    </AbsoluteFill>
  );
};
