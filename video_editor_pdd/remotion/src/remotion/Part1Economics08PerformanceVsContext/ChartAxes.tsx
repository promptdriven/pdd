import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  AXIS_LABEL_COLOR,
  PERFORMANCE_DATA,
  PHASE_AXES_START,
  CHART_PADDING_LEFT,
  CHART_PADDING_RIGHT,
  CHART_PADDING_TOP,
  CHART_PADDING_BOTTOM,
} from './constants';

interface ChartAxesProps {
  chartWidth: number;
  chartHeight: number;
}

const Y_TICKS = [
  { label: '100%', value: 1.0 },
  { label: '75%', value: 0.75 },
  { label: '50%', value: 0.5 },
  { label: '25%', value: 0.25 },
];

/**
 * Draws the X and Y axes, tick marks, and labels for the inset chart.
 */
export const ChartAxes: React.FC<ChartAxesProps> = ({
  chartWidth,
  chartHeight,
}) => {
  const frame = useCurrentFrame();

  const plotLeft = CHART_PADDING_LEFT;
  const plotRight = chartWidth - CHART_PADDING_RIGHT;
  const plotTop = CHART_PADDING_TOP;
  const plotBottom = chartHeight - CHART_PADDING_BOTTOM;
  const plotW = plotRight - plotLeft;
  const plotH = plotBottom - plotTop;

  // Axes draw progress (30 frames from phase start)
  const axisProgress = interpolate(
    frame,
    [PHASE_AXES_START, PHASE_AXES_START + 30],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const axisColor = AXIS_LABEL_COLOR;

  return (
    <svg
      width={chartWidth}
      height={chartHeight}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Y-axis line */}
      <line
        x1={plotLeft}
        y1={plotTop}
        x2={plotLeft}
        y2={plotTop + plotH * axisProgress}
        stroke={axisColor}
        strokeWidth={1}
        opacity={0.6}
      />

      {/* X-axis line */}
      <line
        x1={plotLeft}
        y1={plotBottom}
        x2={plotLeft + plotW * axisProgress}
        y2={plotBottom}
        stroke={axisColor}
        strokeWidth={1}
        opacity={0.6}
      />

      {/* Y-axis ticks and labels */}
      {Y_TICKS.map((tick, i) => {
        const y = plotTop + (1 - tick.value) * plotH;
        const tickOpacity = interpolate(
          axisProgress,
          [0.3, 0.7],
          [0, 0.8],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
        );
        return (
          <g key={`y-${i}`} opacity={tickOpacity}>
            {/* Grid line */}
            <line
              x1={plotLeft}
              y1={y}
              x2={plotRight}
              y2={y}
              stroke={axisColor}
              strokeWidth={0.5}
              opacity={0.2}
              strokeDasharray="4 4"
            />
            {/* Label */}
            <text
              x={plotLeft - 8}
              y={y + 4}
              fill={axisColor}
              fontSize={11}
              fontFamily="Inter, sans-serif"
              fontWeight={400}
              textAnchor="end"
            >
              {tick.label}
            </text>
          </g>
        );
      })}

      {/* X-axis labels */}
      {PERFORMANCE_DATA.map((d, i) => {
        const x = plotLeft + (i / (PERFORMANCE_DATA.length - 1)) * plotW;
        const labelOpacity = interpolate(
          axisProgress,
          [0.5, 1.0],
          [0, 0.8],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
        );
        return (
          <text
            key={`x-${i}`}
            x={x}
            y={plotBottom + 18}
            fill={axisColor}
            fontSize={11}
            fontFamily="Inter, sans-serif"
            fontWeight={400}
            textAnchor="middle"
            opacity={labelOpacity}
          >
            {d.label}
          </text>
        );
      })}

      {/* Y-axis title */}
      <text
        x={14}
        y={plotTop + plotH / 2}
        fill={axisColor}
        fontSize={10}
        fontFamily="Inter, sans-serif"
        fontWeight={400}
        textAnchor="middle"
        transform={`rotate(-90, 14, ${plotTop + plotH / 2})`}
        opacity={interpolate(axisProgress, [0.5, 1], [0, 0.7], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        })}
      >
        Model Performance
      </text>

      {/* X-axis title */}
      <text
        x={plotLeft + plotW / 2}
        y={chartHeight - 4}
        fill={axisColor}
        fontSize={10}
        fontFamily="Inter, sans-serif"
        fontWeight={400}
        textAnchor="middle"
        opacity={interpolate(axisProgress, [0.5, 1], [0, 0.7], {
          extrapolateLeft: 'clamp',
          extrapolateRight: 'clamp',
        })}
      >
        Context length (tokens)
      </text>
    </svg>
  );
};

export default ChartAxes;
