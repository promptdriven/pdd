import React from 'react';
import { AbsoluteFill } from 'remotion';
import { CANVAS, GRID, COLORS } from './constants';

export const GridOverlay: React.FC = () => {
  const verticalLines: number[] = [];
  const horizontalLines: number[] = [];

  for (let x = GRID.spacing; x < CANVAS.width; x += GRID.spacing) {
    verticalLines.push(x);
  }
  for (let y = GRID.spacing; y < CANVAS.height; y += GRID.spacing) {
    horizontalLines.push(y);
  }

  return (
    <AbsoluteFill style={{ opacity: GRID.opacity }}>
      <svg width={CANVAS.width} height={CANVAS.height}>
        {verticalLines.map((x) => (
          <line
            key={`v-${x}`}
            x1={x}
            y1={0}
            x2={x}
            y2={CANVAS.height}
            stroke={COLORS.gridLine}
            strokeWidth={1}
          />
        ))}
        {horizontalLines.map((y) => (
          <line
            key={`h-${y}`}
            x1={0}
            y1={y}
            x2={CANVAS.width}
            y2={y}
            stroke={COLORS.gridLine}
            strokeWidth={1}
          />
        ))}
      </svg>
    </AbsoluteFill>
  );
};
