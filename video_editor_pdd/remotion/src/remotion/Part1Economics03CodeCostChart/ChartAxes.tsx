import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  AXIS_COLOR,
  LABEL_COLOR,
  GRID_COLOR,
  GRID_OPACITY,
  X_MIN,
  X_MAX,
  AXES_DRAW_START,
  AXES_DRAW_END,
  dataToPixelX,
} from './constants';

const GRID_ROWS = 5;
const X_TICK_YEARS = [2000, 2005, 2010, 2015, 2020, 2025];

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [AXES_DRAW_START, AXES_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const yAxisHeight = (CHART_BOTTOM - CHART_TOP) * drawProgress;
  const xAxisWidth = (CHART_RIGHT - CHART_LEFT) * drawProgress;

  const gridSpacing = (CHART_BOTTOM - CHART_TOP) / GRID_ROWS;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Horizontal grid lines */}
      {Array.from({ length: GRID_ROWS + 1 }, (_, i) => {
        const y = CHART_TOP + i * gridSpacing;
        return (
          <line
            key={`grid-h-${i}`}
            x1={CHART_LEFT}
            y1={y}
            x2={CHART_LEFT + xAxisWidth}
            y2={y}
            stroke={GRID_COLOR}
            strokeWidth={1}
            opacity={GRID_OPACITY * drawProgress}
          />
        );
      })}

      {/* Y-axis */}
      <line
        x1={CHART_LEFT}
        y1={CHART_BOTTOM}
        x2={CHART_LEFT}
        y2={CHART_BOTTOM - yAxisHeight}
        stroke={AXIS_COLOR}
        strokeWidth={1.5}
      />

      {/* X-axis */}
      <line
        x1={CHART_LEFT}
        y1={CHART_BOTTOM}
        x2={CHART_LEFT + xAxisWidth}
        y2={CHART_BOTTOM}
        stroke={AXIS_COLOR}
        strokeWidth={1.5}
      />

      {/* Y-axis label */}
      <text
        x={40}
        y={(CHART_TOP + CHART_BOTTOM) / 2}
        fill={LABEL_COLOR}
        fontSize={14}
        fontFamily="Inter, sans-serif"
        fontWeight={400}
        opacity={0.6 * drawProgress}
        textAnchor="middle"
        transform={`rotate(-90, 40, ${(CHART_TOP + CHART_BOTTOM) / 2})`}
      >
        Cost (Developer Hours)
      </text>

      {/* Y-axis tick labels */}
      {[0, 0.25, 0.5, 0.75, 1.0].map((val, i) => {
        const y = CHART_BOTTOM - ((val) / 1.0) * (CHART_BOTTOM - CHART_TOP);
        return (
          <text
            key={`y-label-${i}`}
            x={CHART_LEFT - 12}
            y={y + 4}
            fill={LABEL_COLOR}
            fontSize={12}
            fontFamily="Inter, sans-serif"
            fontWeight={400}
            opacity={0.6 * drawProgress}
            textAnchor="end"
          >
            {val.toFixed(2)}
          </text>
        );
      })}

      {/* X-axis tick marks and labels */}
      {X_TICK_YEARS.filter((yr) => yr >= X_MIN && yr <= X_MAX).map((yr) => {
        const px = dataToPixelX(yr);
        const tickVisible = px <= CHART_LEFT + xAxisWidth ? 1 : 0;
        return (
          <g key={`x-tick-${yr}`} opacity={tickVisible * drawProgress}>
            <line
              x1={px}
              y1={CHART_BOTTOM}
              x2={px}
              y2={CHART_BOTTOM + 8}
              stroke={AXIS_COLOR}
              strokeWidth={1}
            />
            <text
              x={px}
              y={CHART_BOTTOM + 28}
              fill={LABEL_COLOR}
              fontSize={14}
              fontFamily="Inter, sans-serif"
              fontWeight={400}
              opacity={0.6}
              textAnchor="middle"
            >
              {yr}
            </text>
          </g>
        );
      })}
    </svg>
  );
};

export default ChartAxes;
