import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, CHART, type WaveOverlayLayout } from './constants';

export const ChartAxes: React.FC<{ layout: WaveOverlayLayout }> = ({ layout }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [ANIMATION.gridDrawStart, ANIMATION.gridDrawEnd],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const chartHeight = layout.chart.bottom - layout.chart.top;
  const chartWidth = layout.chart.right - layout.chart.left;

  // Y-axis labels
  const yLabels: { value: number; label: string }[] = [];
  for (let v = CHART.yMin; v <= CHART.yMax; v += CHART.yLabelStep) {
    yLabels.push({ value: v, label: v.toFixed(1) });
  }

  // X-axis labels
  const xLabels: { value: number; label: string }[] = [];
  for (let v = CHART.xMin; v <= CHART.xMax; v += CHART.xLabelStep) {
    xLabels.push({ value: v, label: `${v}s` });
  }

  return (
    <svg
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: layout.width,
        height: layout.height,
        opacity,
      }}
    >
      {/* Y-axis line */}
      <line
        x1={layout.chart.left}
        y1={layout.chart.top}
        x2={layout.chart.left}
        y2={layout.chart.bottom}
        stroke={COLORS.axisLabel}
        strokeWidth={1}
      />
      {/* X-axis line */}
      <line
        x1={layout.chart.left}
        y1={layout.chart.bottom}
        x2={layout.chart.right}
        y2={layout.chart.bottom}
        stroke={COLORS.axisLabel}
        strokeWidth={1}
      />

      {/* Y-axis labels */}
      {yLabels.map(({ value, label }) => {
        const yNorm = (value - CHART.yMin) / (CHART.yMax - CHART.yMin);
        const yPx = layout.chart.bottom - yNorm * chartHeight;
        return (
          <text
            key={`y-${value}`}
            x={layout.chart.left - 10 * layout.scaleX}
            y={yPx + 4 * layout.scaleY}
            textAnchor="end"
            fill={COLORS.axisLabel}
            fontFamily={layout.typography.axisLabel.fontFamily}
            fontSize={layout.typography.axisLabel.fontSize}
            fontWeight={layout.typography.axisLabel.fontWeight}
          >
            {label}
          </text>
        );
      })}

      {/* X-axis labels */}
      {xLabels.map(({ value, label }) => {
        const xNorm = (value - CHART.xMin) / (CHART.xMax - CHART.xMin);
        const xPx = layout.chart.left + xNorm * chartWidth;
        return (
          <text
            key={`x-${value}`}
            x={xPx}
            y={layout.chart.bottom + 24 * layout.scaleY}
            textAnchor="middle"
            fill={COLORS.axisLabel}
            fontFamily={layout.typography.axisLabel.fontFamily}
            fontSize={layout.typography.axisLabel.fontSize}
            fontWeight={layout.typography.axisLabel.fontWeight}
          >
            {label}
          </text>
        );
      })}
    </svg>
  );
};
