import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { CHART_CONFIG, ANIMATION_TIMING } from './constants';

export const GridLines: React.FC = () => {
  const frame = useCurrentFrame();
  const { chartArea, colors, grid, strokeWidths } = CHART_CONFIG;
  const { start, duration } = ANIMATION_TIMING.gridFadeIn;

  const chartX = chartArea.marginLeft;
  const chartY = chartArea.marginTop;
  const chartWidth = chartArea.width;
  const chartHeight = chartArea.height;

  const gridOpacity = interpolate(
    frame,
    [start, start + duration],
    [0, grid.opacity],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.ease),
    }
  );

  const horizontalLines = Array.from({ length: grid.rows }, (_, i) => {
    const y = chartY + (chartHeight / (grid.rows - 1)) * i;
    const lineDelay = i * 2;
    const lineOpacity = interpolate(
      frame,
      [start + lineDelay, start + lineDelay + duration / 2],
      [0, gridOpacity],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      }
    );

    return (
      <line
        key={`h-${i}`}
        x1={chartX}
        y1={y}
        x2={chartX + chartWidth}
        y2={y}
        stroke={colors.gridLine}
        strokeWidth={strokeWidths.gridLine}
        opacity={lineOpacity}
      />
    );
  });

  const verticalLines = Array.from({ length: grid.cols }, (_, i) => {
    const x = chartX + (chartWidth / (grid.cols - 1)) * i;
    const lineDelay = i * 2;
    const lineOpacity = interpolate(
      frame,
      [start + lineDelay, start + lineDelay + duration / 2],
      [0, gridOpacity],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      }
    );

    return (
      <line
        key={`v-${i}`}
        x1={x}
        y1={chartY}
        x2={x}
        y2={chartY + chartHeight}
        stroke={colors.gridLine}
        strokeWidth={strokeWidths.gridLine}
        opacity={lineOpacity}
      />
    );
  });

  return (
    <svg
      width={CHART_CONFIG.width}
      height={CHART_CONFIG.height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {horizontalLines}
      {verticalLines}
    </svg>
  );
};
