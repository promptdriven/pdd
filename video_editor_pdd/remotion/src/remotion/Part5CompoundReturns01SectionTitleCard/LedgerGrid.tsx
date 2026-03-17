import React from 'react';
import { AbsoluteFill } from 'remotion';
import { CANVAS, GRID, COLORS } from './constants';

export const LedgerGrid: React.FC = () => {
  const horizontalLines: React.ReactNode[] = [];
  const verticalLines: React.ReactNode[] = [];

  for (let y = 0; y <= CANVAS.height; y += GRID.hSpacing) {
    horizontalLines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={CANVAS.width}
        y2={y}
        stroke={COLORS.gridLine}
        strokeWidth={1}
        opacity={GRID.hOpacity}
      />
    );
  }

  for (let x = 0; x <= CANVAS.width; x += GRID.vAccentEvery) {
    verticalLines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={CANVAS.height}
        stroke={COLORS.gridLine}
        strokeWidth={1}
        opacity={GRID.vOpacity}
      />
    );
  }

  return (
    <AbsoluteFill>
      <svg
        width={CANVAS.width}
        height={CANVAS.height}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        {horizontalLines}
        {verticalLines}
      </svg>
    </AbsoluteFill>
  );
};
