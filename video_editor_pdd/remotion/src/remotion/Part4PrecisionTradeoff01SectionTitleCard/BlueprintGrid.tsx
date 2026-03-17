import React from 'react';
import { AbsoluteFill } from 'remotion';
import { CANVAS, GRID } from './constants';

export const BlueprintGrid: React.FC<{ opacity: number }> = ({ opacity }) => {
  const { SPACING, COLOR } = GRID;
  const lines: React.ReactNode[] = [];

  // Vertical lines
  for (let x = 0; x <= CANVAS.WIDTH; x += SPACING) {
    lines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={CANVAS.HEIGHT}
        stroke={COLOR}
        strokeWidth={0.5}
      />
    );
  }

  // Horizontal lines
  for (let y = 0; y <= CANVAS.HEIGHT; y += SPACING) {
    lines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={CANVAS.WIDTH}
        y2={y}
        stroke={COLOR}
        strokeWidth={0.5}
      />
    );
  }

  return (
    <AbsoluteFill style={{ opacity: GRID.OPACITY * opacity }}>
      <svg
        width={CANVAS.WIDTH}
        height={CANVAS.HEIGHT}
        viewBox={`0 0 ${CANVAS.WIDTH} ${CANVAS.HEIGHT}`}
      >
        {lines}
      </svg>
    </AbsoluteFill>
  );
};
