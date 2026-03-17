import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, CHART, X_LABELS, TIMING } from './constants';

export const ChartGrid: React.FC = () => {
  const frame = useCurrentFrame();

  const axisProgress = interpolate(
    frame,
    [TIMING.axesStart, TIMING.axesStart + 20],
    [0, 1],
    { extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Horizontal grid lines
  const hLines: number[] = [];
  for (let y = CHART.originY; y > 60; y -= CHART.gridHSpacing) {
    hLines.push(y);
  }

  // Vertical grid lines at year markers
  const vLines = X_LABELS.map((l) => l.x);

  return (
    <svg
      width={CHART.width}
      height={CHART.height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Horizontal grid lines */}
      {hLines.map((y, i) => (
        <line
          key={`h-${i}`}
          x1={CHART.yAxisX}
          y1={y}
          x2={CHART.yAxisX + (CHART.endX - CHART.yAxisX) * axisProgress}
          y2={y}
          stroke={COLORS.gridLine}
          strokeWidth={1}
          opacity={0.05}
        />
      ))}

      {/* Vertical grid lines */}
      {vLines.map((x, i) => (
        <line
          key={`v-${i}`}
          x1={x}
          y1={CHART.xAxisY}
          x2={x}
          y2={CHART.xAxisY - (CHART.xAxisY - 60) * axisProgress}
          stroke={COLORS.gridLine}
          strokeWidth={1}
          opacity={0.05}
        />
      ))}

      {/* X-axis */}
      <line
        x1={CHART.yAxisX}
        y1={CHART.xAxisY}
        x2={CHART.yAxisX + (CHART.endX - CHART.yAxisX + 40) * axisProgress}
        y2={CHART.xAxisY}
        stroke={COLORS.axis}
        strokeWidth={2}
        opacity={0.4}
      />

      {/* Y-axis */}
      <line
        x1={CHART.yAxisX}
        y1={CHART.xAxisY}
        x2={CHART.yAxisX}
        y2={CHART.xAxisY - (CHART.xAxisY - 60) * axisProgress}
        stroke={COLORS.axis}
        strokeWidth={2}
        opacity={0.4}
      />

      {/* X-axis labels */}
      {X_LABELS.map((label, i) => (
        <text
          key={`xl-${i}`}
          x={label.x}
          y={CHART.xAxisY + 28}
          textAnchor="middle"
          fontFamily="Inter, sans-serif"
          fontSize={12}
          fill={COLORS.axisLabel}
          opacity={0.4 * axisProgress}
        >
          {label.text}
        </text>
      ))}

      {/* Y-axis label (rotated) */}
      <text
        x={CHART.yAxisX - 45}
        y={(CHART.xAxisY + 60) / 2}
        textAnchor="middle"
        fontFamily="Inter, sans-serif"
        fontSize={12}
        fill={COLORS.axisLabel}
        opacity={0.4 * axisProgress}
        transform={`rotate(-90, ${CHART.yAxisX - 45}, ${(CHART.xAxisY + 60) / 2})`}
      >
        Cumulative Cost
      </text>

      {/* Origin point */}
      <circle
        cx={CHART.originX}
        cy={CHART.originY}
        r={6}
        fill={COLORS.text}
        opacity={0.6 * axisProgress}
      />
      <text
        x={CHART.originX}
        y={CHART.originY + 24}
        textAnchor="middle"
        fontFamily="Inter, sans-serif"
        fontSize={11}
        fill={COLORS.text}
        opacity={0.4 * axisProgress}
      >
        Today
      </text>
    </svg>
  );
};
