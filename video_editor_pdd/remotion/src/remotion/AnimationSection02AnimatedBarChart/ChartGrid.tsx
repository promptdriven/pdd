import React from 'react';
import { interpolate, useCurrentFrame } from 'remotion';
import { COLORS, DIMENSIONS, MAX_VALUE, GRID_LINES, TIMING } from './constants';

interface ChartGridProps {
  centerX: number;
  centerY: number;
}

export const ChartGrid: React.FC<ChartGridProps> = ({ centerX, centerY }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [TIMING.gridFadeStart, TIMING.gridFadeStart + TIMING.gridFadeDuration],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  const chartLeft = centerX - DIMENSIONS.chartWidth / 2;
  const chartTop = centerY - DIMENSIONS.chartHeight / 2;
  const chartRight = centerX + DIMENSIONS.chartWidth / 2;
  const chartBottom = centerY + DIMENSIONS.chartHeight / 2;

  const gridLineCount = GRID_LINES + 1; // 0, 25, 50, 75, 100
  const lines = [];

  for (let i = 0; i < gridLineCount; i++) {
    const y = chartBottom - (i / GRID_LINES) * DIMENSIONS.chartHeight;
    lines.push(
      <line
        key={i}
        x1={chartLeft}
        y1={y}
        x2={chartRight}
        y2={y}
        stroke={COLORS.gridLine}
        strokeWidth={1}
        opacity={opacity}
      />
    );
  }

  return <>{lines}</>;
};
