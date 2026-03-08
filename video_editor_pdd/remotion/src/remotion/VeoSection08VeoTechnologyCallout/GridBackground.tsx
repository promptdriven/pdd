import React from 'react';
import { CANVAS, COLORS } from './constants';

const GRID_SPACING = 60;

export const GridBackground: React.FC = () => {
  const verticalLines = Math.floor(CANVAS.width / GRID_SPACING);
  const horizontalLines = Math.floor(CANVAS.height / GRID_SPACING);

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: CANVAS.width,
        height: CANVAS.height,
        overflow: 'hidden',
        pointerEvents: 'none',
      }}
    >
      {/* Vertical grid lines */}
      {Array.from({ length: verticalLines }).map((_, i) => (
        <div
          key={`v${i}`}
          style={{
            position: 'absolute',
            left: (i + 1) * GRID_SPACING,
            top: 0,
            width: 1,
            height: CANVAS.height,
            backgroundColor: COLORS.gridLine,
          }}
        />
      ))}
      {/* Horizontal grid lines */}
      {Array.from({ length: horizontalLines }).map((_, i) => (
        <div
          key={`h${i}`}
          style={{
            position: 'absolute',
            left: 0,
            top: (i + 1) * GRID_SPACING,
            width: CANVAS.width,
            height: 1,
            backgroundColor: COLORS.gridLine,
          }}
        />
      ))}
    </div>
  );
};
