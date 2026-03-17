import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  WIDTH,
  HEIGHT,
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  AXIS_COLOR,
  AXIS_OPACITY,
  LABEL_COLOR,
  LABEL_OPACITY,
  X_LABELS,
  Y_LABELS,
  AXES_DRAW_START,
  AXES_DRAW_DURATION,
} from './constants';

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [AXES_DRAW_START, AXES_DRAW_START + AXES_DRAW_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const labelOpacity = interpolate(
    frame,
    [AXES_DRAW_START + 5, AXES_DRAW_START + AXES_DRAW_DURATION + 10],
    [0, LABEL_OPACITY],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    },
  );

  // X-axis: horizontal line at CHART_BOTTOM
  const xAxisEndX = CHART_LEFT + (CHART_RIGHT - CHART_LEFT) * drawProgress;
  // Y-axis: vertical line at CHART_LEFT
  const yAxisEndY = CHART_BOTTOM - (CHART_BOTTOM - CHART_TOP) * drawProgress;

  // X-axis label positions (evenly distributed)
  const xLabelPositions = X_LABELS.map((_, i) => {
    const t = i / (X_LABELS.length - 1);
    return CHART_LEFT + t * (CHART_RIGHT - CHART_LEFT);
  });

  // Y-axis label positions (evenly distributed)
  const yLabelPositions = Y_LABELS.map((_, i) => {
    const t = i / (Y_LABELS.length - 1);
    return CHART_BOTTOM - t * (CHART_BOTTOM - CHART_TOP);
  });

  return (
    <>
      <svg
        width={WIDTH}
        height={HEIGHT}
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
          opacity={AXIS_OPACITY}
        />
        {/* Y-axis line */}
        <line
          x1={CHART_LEFT}
          y1={CHART_BOTTOM}
          x2={CHART_LEFT}
          y2={yAxisEndY}
          stroke={AXIS_COLOR}
          strokeWidth={2}
          opacity={AXIS_OPACITY}
        />

        {/* X-axis label: "Time" */}
        <text
          x={(CHART_LEFT + CHART_RIGHT) / 2}
          y={CHART_BOTTOM + 60}
          textAnchor="middle"
          fill={LABEL_COLOR}
          opacity={labelOpacity}
          fontFamily="Inter, sans-serif"
          fontSize={14}
          fontWeight={500}
        >
          Time
        </text>

        {/* Y-axis label: "Cost" */}
        <text
          x={CHART_LEFT - 60}
          y={(CHART_TOP + CHART_BOTTOM) / 2}
          textAnchor="middle"
          fill={LABEL_COLOR}
          opacity={labelOpacity}
          fontFamily="Inter, sans-serif"
          fontSize={14}
          fontWeight={500}
          transform={`rotate(-90, ${CHART_LEFT - 60}, ${(CHART_TOP + CHART_BOTTOM) / 2})`}
        >
          Cost
        </text>

        {/* X-axis tick labels */}
        {X_LABELS.map((label, i) => (
          <text
            key={`x-label-${i}`}
            x={xLabelPositions[i]}
            y={CHART_BOTTOM + 30}
            textAnchor="middle"
            fill={LABEL_COLOR}
            opacity={labelOpacity}
            fontFamily="Inter, sans-serif"
            fontSize={11}
          >
            {label}
          </text>
        ))}

        {/* Y-axis tick labels */}
        {Y_LABELS.map((label, i) => (
          <text
            key={`y-label-${i}`}
            x={CHART_LEFT - 20}
            y={yLabelPositions[i] + 4}
            textAnchor="end"
            fill={LABEL_COLOR}
            opacity={labelOpacity}
            fontFamily="Inter, sans-serif"
            fontSize={11}
          >
            {label}
          </text>
        ))}
      </svg>
    </>
  );
};
