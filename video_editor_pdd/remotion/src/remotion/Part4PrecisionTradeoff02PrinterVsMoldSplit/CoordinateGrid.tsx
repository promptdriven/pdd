import React from 'react';
import { GRID, COLORS } from './constants';

/**
 * Renders the 20x20 coordinate grid with animated dot activation
 * as the printer nozzle traverses.
 */
export const CoordinateGrid: React.FC<{
  gridAppearProgress: number;
  activeDotCount: number;
}> = ({ gridAppearProgress, activeDotCount }) => {
  const { rows, cols, spacing, centerX, centerY, dotRadius, activeDotRadius } =
    GRID;

  // Compute grid origin (top-left)
  const originX = centerX - ((cols - 1) * spacing) / 2;
  const originY = centerY - ((rows - 1) * spacing) / 2;

  // Build arrays of grid lines and dots
  const gridLines: React.ReactNode[] = [];
  const dots: React.ReactNode[] = [];

  // Horizontal grid lines
  for (let r = 0; r < rows; r++) {
    const y = originY + r * spacing;
    gridLines.push(
      <line
        key={`h-${r}`}
        x1={originX}
        y1={y}
        x2={originX + (cols - 1) * spacing}
        y2={y}
        stroke={COLORS.gridLine}
        strokeOpacity={0.15 * gridAppearProgress}
        strokeWidth={1}
      />
    );
  }
  // Vertical grid lines
  for (let c = 0; c < cols; c++) {
    const x = originX + c * spacing;
    gridLines.push(
      <line
        key={`v-${c}`}
        x1={x}
        y1={originY}
        x2={x}
        y2={originY + (rows - 1) * spacing}
        stroke={COLORS.gridLine}
        strokeOpacity={0.15 * gridAppearProgress}
        strokeWidth={1}
      />
    );
  }

  // Dots at intersections
  for (let r = 0; r < rows; r++) {
    for (let c = 0; c < cols; c++) {
      const idx = r * cols + c;
      const x = originX + c * spacing;
      const y = originY + r * spacing;
      const isActive = idx < activeDotCount;

      dots.push(
        <circle
          key={`d-${r}-${c}`}
          cx={x}
          cy={y}
          r={isActive ? activeDotRadius : dotRadius}
          fill={isActive ? COLORS.activeDot : COLORS.gridDot}
          opacity={
            isActive ? 0.8 : 0.3 * gridAppearProgress
          }
        />
      );
    }
  }

  return (
    <svg
      width={958}
      height={860}
      style={{ position: 'absolute', top: 60, left: 0 }}
    >
      <g opacity={gridAppearProgress}>
        {gridLines}
      </g>
      {dots}
    </svg>
  );
};
