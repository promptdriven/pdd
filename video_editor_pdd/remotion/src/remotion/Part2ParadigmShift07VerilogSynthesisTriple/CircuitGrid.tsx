import React from 'react';
import { AbsoluteFill } from 'remotion';
import { GRID_COLOR, GRID_OPACITY, GRID_SPACING, WIDTH, HEIGHT } from './constants';

export const CircuitGrid: React.FC = () => {
  const verticalLines: number[] = [];
  const horizontalLines: number[] = [];

  for (let x = 0; x <= WIDTH; x += GRID_SPACING) {
    verticalLines.push(x);
  }
  for (let y = 0; y <= HEIGHT; y += GRID_SPACING) {
    horizontalLines.push(y);
  }

  return (
    <AbsoluteFill>
      <svg width={WIDTH} height={HEIGHT} style={{ position: 'absolute', top: 0, left: 0 }}>
        {verticalLines.map((x) => (
          <line
            key={`v-${x}`}
            x1={x}
            y1={0}
            x2={x}
            y2={HEIGHT}
            stroke={GRID_COLOR}
            strokeWidth={1}
            opacity={GRID_OPACITY}
          />
        ))}
        {horizontalLines.map((y) => (
          <line
            key={`h-${y}`}
            x1={0}
            y1={y}
            x2={WIDTH}
            y2={y}
            stroke={GRID_COLOR}
            strokeWidth={1}
            opacity={GRID_OPACITY}
          />
        ))}
      </svg>
    </AbsoluteFill>
  );
};
