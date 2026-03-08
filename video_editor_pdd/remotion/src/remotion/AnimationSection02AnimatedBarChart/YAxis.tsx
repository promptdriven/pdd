import React from 'react';
import { interpolate, useCurrentFrame } from 'remotion';
import { COLORS, DIMENSIONS, MAX_VALUE, GRID_LINES, TIMING, TYPOGRAPHY } from './constants';

interface YAxisProps {
  centerX: number;
  centerY: number;
}

export const YAxis: React.FC<YAxisProps> = ({ centerX, centerY }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [TIMING.gridFadeStart, TIMING.gridFadeStart + TIMING.gridFadeDuration],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  const chartLeft = centerX - DIMENSIONS.chartWidth / 2;
  const chartBottom = centerY + DIMENSIONS.chartHeight / 2;

  const labels = [0, 25, 50, 75, 100];

  return (
    <>
      {labels.map((value, index) => {
        const y = chartBottom - (index / GRID_LINES) * DIMENSIONS.chartHeight;
        return (
          <text
            key={value}
            x={chartLeft - 40}
            y={y + 6}
            fill={COLORS.axisLabel}
            fontSize={TYPOGRAPHY.axisLabelSize}
            fontFamily={TYPOGRAPHY.fontFamily}
            fontWeight="500"
            textAnchor="end"
            opacity={opacity}
          >
            {value}
          </text>
        );
      })}
    </>
  );
};
