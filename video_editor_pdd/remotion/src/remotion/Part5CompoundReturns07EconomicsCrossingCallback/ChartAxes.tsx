// ChartAxes.tsx — Grid lines, axis lines, and axis labels (morphable)
import React from 'react';
import { CHART, COLORS, OPACITIES, Y_RANGE } from './constants';

interface ChartAxesProps {
  /** X-axis labels to display */
  xLabels: string[];
  /** Opacity of the entire axes group */
  opacity: number;
}

/**
 * Renders the chart grid, axes, and labels.
 * Labels are provided externally so the parent can morph them.
 */
export const ChartAxes: React.FC<ChartAxesProps> = ({ xLabels, opacity }) => {
  const { left, top, width, height } = CHART;

  // Horizontal grid lines at $5 intervals (0, 5, 10, 15, 20, 25, 30)
  const yTicks = [0, 5, 10, 15, 20, 25, 30];

  return (
    <div style={{ position: 'absolute', inset: 0, opacity }}>
      {/* SVG for grid + axes */}
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        {/* Horizontal grid lines */}
        {yTicks.map((val) => {
          const yPos = top + height - (val / Y_RANGE.max) * height;
          return (
            <line
              key={`hgrid-${val}`}
              x1={left}
              y1={yPos}
              x2={left + width}
              y2={yPos}
              stroke={COLORS.gridLine}
              strokeOpacity={OPACITIES.gridLine}
              strokeWidth={1}
            />
          );
        })}

        {/* Vertical grid lines for each label */}
        {xLabels.map((_, i) => {
          const xPos = left + (i / (xLabels.length - 1)) * width;
          return (
            <line
              key={`vgrid-${i}`}
              x1={xPos}
              y1={top}
              x2={xPos}
              y2={top + height}
              stroke={COLORS.gridLine}
              strokeOpacity={OPACITIES.gridLine}
              strokeWidth={1}
            />
          );
        })}

        {/* X-axis baseline */}
        <line
          x1={left}
          y1={top + height}
          x2={left + width}
          y2={top + height}
          stroke={COLORS.axisLabel}
          strokeOpacity={0.3}
          strokeWidth={1}
        />

        {/* Y-axis baseline */}
        <line
          x1={left}
          y1={top}
          x2={left}
          y2={top + height}
          stroke={COLORS.axisLabel}
          strokeOpacity={0.3}
          strokeWidth={1}
        />
      </svg>

      {/* Y-axis labels */}
      {yTicks.map((val) => {
        const yPos = top + height - (val / Y_RANGE.max) * height;
        return (
          <div
            key={`ylabel-${val}`}
            style={{
              position: 'absolute',
              right: 1920 - left + 10,
              top: yPos - 8,
              fontFamily: 'Inter, sans-serif',
              fontSize: 12,
              color: COLORS.axisLabel,
              opacity: OPACITIES.axisLabel,
              textAlign: 'right',
              width: 40,
            }}
          >
            ${val}
          </div>
        );
      })}

      {/* X-axis labels */}
      {xLabels.map((label, i) => {
        const xPos = left + (i / (xLabels.length - 1)) * width;
        return (
          <div
            key={`xlabel-${i}`}
            style={{
              position: 'absolute',
              left: xPos,
              top: top + height + 12,
              transform: 'translateX(-50%)',
              fontFamily: 'Inter, sans-serif',
              fontSize: 12,
              color: COLORS.axisLabel,
              opacity: OPACITIES.axisLabel,
              whiteSpace: 'nowrap',
            }}
          >
            {label}
          </div>
        );
      })}
    </div>
  );
};

export default ChartAxes;
