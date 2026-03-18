import React from 'react';
import { GRID, COLORS } from './constants';

/**
 * Renders the 3D printer nozzle as an inverted triangle
 * that tracks across the grid based on the current active dot index.
 */
export const PrinterNozzle: React.FC<{
  activeDotCount: number;
  visible: boolean;
}> = ({ activeDotCount, visible }) => {
  if (!visible || activeDotCount < 0) return null;

  const { rows, cols, spacing, centerX, centerY } = GRID;
  const originX = centerX - ((cols - 1) * spacing) / 2;
  const originY = centerY - ((rows - 1) * spacing) / 2;

  // Clamp to valid range
  const idx = Math.min(activeDotCount, rows * cols - 1);
  const row = Math.floor(idx / cols);
  const col = idx % cols;

  const x = originX + col * spacing;
  const y = originY + row * spacing;

  const nozzleSize = 12;

  return (
    <svg
      width={958}
      height={860}
      style={{ position: 'absolute', top: 60, left: 0, pointerEvents: 'none' }}
    >
      {/* Inverted triangle nozzle */}
      <polygon
        points={`${x - nozzleSize},${y - nozzleSize - 4} ${x + nozzleSize},${y - nozzleSize - 4} ${x},${y - 2}`}
        fill={COLORS.nozzle}
        opacity={0.6}
      />
      {/* Small circle at tip */}
      <circle cx={x} cy={y - 1} r={2} fill={COLORS.nozzle} opacity={0.8} />
    </svg>
  );
};
