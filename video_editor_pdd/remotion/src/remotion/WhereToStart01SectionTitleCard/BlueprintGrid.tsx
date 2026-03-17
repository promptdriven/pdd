import React from 'react';
import { AbsoluteFill } from 'remotion';
import { CANVAS, GRID } from './constants';

export const BlueprintGrid: React.FC<{ opacity: number }> = ({ opacity }) => {
  const lines: React.ReactNode[] = [];
  const { WIDTH, HEIGHT } = CANVAS;
  const { SPACING, COLOR } = GRID;

  // Vertical lines
  for (let x = 0; x <= WIDTH; x += SPACING) {
    lines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={HEIGHT}
        stroke={COLOR}
        strokeWidth={1}
      />,
    );
  }
  // Horizontal lines
  for (let y = 0; y <= HEIGHT; y += SPACING) {
    lines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={WIDTH}
        y2={y}
        stroke={COLOR}
        strokeWidth={1}
      />,
    );
  }

  return (
    <AbsoluteFill style={{ opacity: opacity * GRID.OPACITY }}>
      <svg width={WIDTH} height={HEIGHT} viewBox={`0 0 ${WIDTH} ${HEIGHT}`}>
        {lines}
      </svg>
    </AbsoluteFill>
  );
};
