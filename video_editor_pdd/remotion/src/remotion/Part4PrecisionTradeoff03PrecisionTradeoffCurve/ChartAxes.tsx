import React from 'react';
import { useCurrentFrame, Easing, interpolate } from 'remotion';
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  AXIS_COLOR,
  AXIS_LABEL_COLOR,
  X_TICKS,
  Y_TICK_LABELS,
  ANIM,
} from './constants';

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  // Axes draw progress (0-30 frames)
  const axisProgress = interpolate(
    frame,
    [ANIM.AXES_START, ANIM.AXES_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    }
  );

  // Ticks and labels fade (30-60 frames)
  const tickOpacity = interpolate(
    frame,
    [ANIM.TICKS_START, ANIM.TICKS_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    }
  );

  // X-axis: horizontal line
  const xAxisEndX = CHART_LEFT + (CHART_RIGHT - CHART_LEFT) * axisProgress;
  // Y-axis: vertical line (draws from bottom up)
  const yAxisEndY = CHART_BOTTOM - (CHART_BOTTOM - CHART_TOP) * axisProgress;

  const xTickSpacing = (CHART_RIGHT - CHART_LEFT) / 50;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* X-axis line */}
      <line
        x1={CHART_LEFT}
        y1={CHART_BOTTOM}
        x2={xAxisEndX}
        y2={CHART_BOTTOM}
        stroke={AXIS_COLOR}
        strokeWidth={2}
        strokeOpacity={0.4}
      />

      {/* Y-axis line */}
      <line
        x1={CHART_LEFT}
        y1={CHART_BOTTOM}
        x2={CHART_LEFT}
        y2={yAxisEndY}
        stroke={AXIS_COLOR}
        strokeWidth={2}
        strokeOpacity={0.4}
      />

      {/* X-axis ticks and labels */}
      {X_TICKS.map((tick) => {
        const x = CHART_LEFT + tick * xTickSpacing;
        return (
          <g key={`x-tick-${tick}`} opacity={tickOpacity}>
            <line
              x1={x}
              y1={CHART_BOTTOM}
              x2={x}
              y2={CHART_BOTTOM + 6}
              stroke={AXIS_COLOR}
              strokeWidth={1}
              strokeOpacity={0.3}
            />
            <text
              x={x}
              y={CHART_BOTTOM + 22}
              textAnchor="middle"
              fill={AXIS_LABEL_COLOR}
              fillOpacity={0.3}
              fontSize={10}
              fontFamily="Inter, sans-serif"
            >
              {tick}
            </text>
          </g>
        );
      })}

      {/* Y-axis tick labels */}
      {Y_TICK_LABELS.map((label, i) => {
        const yRange = CHART_BOTTOM - CHART_TOP;
        // "Low" at bottom, "High" at top
        const y = CHART_BOTTOM - (i / (Y_TICK_LABELS.length - 1)) * yRange;
        return (
          <g key={`y-tick-${label}`} opacity={tickOpacity}>
            <line
              x1={CHART_LEFT - 6}
              y1={y}
              x2={CHART_LEFT}
              y2={y}
              stroke={AXIS_COLOR}
              strokeWidth={1}
              strokeOpacity={0.3}
            />
            <text
              x={CHART_LEFT - 12}
              y={y + 4}
              textAnchor="end"
              fill={AXIS_LABEL_COLOR}
              fillOpacity={0.3}
              fontSize={10}
              fontFamily="Inter, sans-serif"
            >
              {label}
            </text>
          </g>
        );
      })}

      {/* X-axis label */}
      <text
        x={CHART_RIGHT}
        y={CHART_BOTTOM + 48}
        textAnchor="end"
        fill={AXIS_LABEL_COLOR}
        fillOpacity={0.5 * tickOpacity}
        fontSize={12}
        fontFamily="Inter, sans-serif"
      >
        {'Number of Tests →'}
      </text>

      {/* Y-axis label (rotated) */}
      <text
        x={CHART_LEFT - 55}
        y={(CHART_TOP + CHART_BOTTOM) / 2}
        textAnchor="middle"
        fill={AXIS_LABEL_COLOR}
        fillOpacity={0.5 * tickOpacity}
        fontSize={12}
        fontFamily="Inter, sans-serif"
        transform={`rotate(-90, ${CHART_LEFT - 55}, ${(CHART_TOP + CHART_BOTTOM) / 2})`}
      >
        {'Required Prompt Precision ↑'}
      </text>
    </svg>
  );
};
