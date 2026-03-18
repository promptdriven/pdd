import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { CHART, COLORS, TIMING, X_TICKS, Y_TICK_LABELS } from './constants';

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  // Axes draw progress (0-30 frames)
  const axisProgress = interpolate(
    frame,
    [TIMING.axesDrawStart, TIMING.axesDrawEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.cubic) }
  );

  // Ticks and labels fade (30-60 frames)
  const tickOpacity = interpolate(
    frame,
    [TIMING.ticksStart, TIMING.ticksEnd],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  const xAxisWidth = CHART.width * axisProgress;
  const yAxisHeight = (CHART.originY - CHART.topY) * axisProgress;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* X-axis */}
      <line
        x1={CHART.originX}
        y1={CHART.originY}
        x2={CHART.originX + xAxisWidth}
        y2={CHART.originY}
        stroke={COLORS.axisLine}
        strokeOpacity={0.4}
        strokeWidth={2}
      />

      {/* Y-axis */}
      <line
        x1={CHART.originX}
        y1={CHART.originY}
        x2={CHART.originX}
        y2={CHART.originY - yAxisHeight}
        stroke={COLORS.axisLine}
        strokeOpacity={0.4}
        strokeWidth={2}
      />

      {/* X-axis label */}
      <text
        x={CHART.endX}
        y={CHART.originY + 45}
        fill={COLORS.axisLabel}
        opacity={tickOpacity * 0.5}
        fontSize={12}
        fontFamily="Inter, sans-serif"
        textAnchor="end"
      >
        Number of Tests →
      </text>

      {/* Y-axis label (rotated) */}
      <text
        x={CHART.originX - 50}
        y={(CHART.originY + CHART.topY) / 2}
        fill={COLORS.axisLabel}
        opacity={tickOpacity * 0.5}
        fontSize={12}
        fontFamily="Inter, sans-serif"
        textAnchor="middle"
        transform={`rotate(-90, ${CHART.originX - 50}, ${(CHART.originY + CHART.topY) / 2})`}
      >
        Required Prompt Precision ↑
      </text>

      {/* X-axis tick marks and labels */}
      {X_TICKS.map((tick) => {
        const x = CHART.originX + (tick / 50) * CHART.width;
        return (
          <g key={`x-tick-${tick}`} opacity={tickOpacity}>
            <line
              x1={x}
              y1={CHART.originY}
              x2={x}
              y2={CHART.originY + 6}
              stroke={COLORS.axisLine}
              strokeOpacity={0.3}
              strokeWidth={1}
            />
            <text
              x={x}
              y={CHART.originY + 22}
              fill={COLORS.axisLabel}
              opacity={0.3}
              fontSize={10}
              fontFamily="Inter, sans-serif"
              textAnchor="middle"
            >
              {tick}
            </text>
          </g>
        );
      })}

      {/* Y-axis tick labels */}
      {Y_TICK_LABELS.map((label, i) => {
        const y = CHART.originY - ((i + 1) / (Y_TICK_LABELS.length + 1)) * (CHART.originY - CHART.topY);
        return (
          <text
            key={`y-tick-${label}`}
            x={CHART.originX - 15}
            y={y + 4}
            fill={COLORS.axisLabel}
            opacity={tickOpacity * 0.3}
            fontSize={10}
            fontFamily="Inter, sans-serif"
            textAnchor="end"
          >
            {label}
          </text>
        );
      })}
    </svg>
  );
};
