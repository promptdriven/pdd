import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS, GRID_SPACING, GRID_OPACITY, CANVAS } from './constants';

export const EngineeringGrid: React.FC = () => {
  const lines: React.ReactNode[] = [];

  // Vertical lines
  for (let x = 0; x <= CANVAS.width; x += GRID_SPACING) {
    lines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={CANVAS.height}
        stroke={COLORS.gridLine}
        strokeWidth={1}
        opacity={GRID_OPACITY}
      />
    );
  }

  // Horizontal lines
  for (let y = 0; y <= CANVAS.height; y += GRID_SPACING) {
    lines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={CANVAS.width}
        y2={y}
        stroke={COLORS.gridLine}
        strokeWidth={1}
        opacity={GRID_OPACITY}
      />
    );
  }

  return (
    <AbsoluteFill>
      <svg width={CANVAS.width} height={CANVAS.height}>
        {lines}
      </svg>
    </AbsoluteFill>
  );
};
