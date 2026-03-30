import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  CHART_HEIGHT,
  GRID_SPACING,
  GRID_COLOR,
  GRID_OPACITY,
  AXIS_COLOR,
  AXIS_LABEL_COLOR,
  X_MIN,
  X_MAX,
  AXES_DRAW_START,
  AXES_DRAW_END,
  mapX,
} from "./constants";

const X_TICK_YEARS = [2000, 2005, 2010, 2015, 2020, 2025];
const Y_TICK_COUNT = 5; // 0, 0.25, 0.5, 0.75, 1.0

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [AXES_DRAW_START, AXES_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const axisOpacity = interpolate(frame, [AXES_DRAW_START, AXES_DRAW_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Horizontal grid lines
  const gridLines: React.ReactNode[] = [];
  const numGridLines = Math.floor(CHART_HEIGHT / GRID_SPACING);
  for (let i = 1; i <= numGridLines; i++) {
    const y = CHART_BOTTOM - i * GRID_SPACING;
    if (y < CHART_TOP) break;
    const lineWidth = (CHART_RIGHT - CHART_LEFT) * drawProgress;
    gridLines.push(
      <line
        key={`grid-h-${i}`}
        x1={CHART_LEFT}
        y1={y}
        x2={CHART_LEFT + lineWidth}
        y2={y}
        stroke={GRID_COLOR}
        strokeWidth={1}
        opacity={GRID_OPACITY}
      />
    );
  }

  // Y-axis line
  const yAxisHeight = (CHART_BOTTOM - CHART_TOP) * drawProgress;

  // X-axis line
  const xAxisWidth = (CHART_RIGHT - CHART_LEFT) * drawProgress;

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Grid lines */}
      {gridLines}

      {/* Y-axis */}
      <line
        x1={CHART_LEFT}
        y1={CHART_BOTTOM}
        x2={CHART_LEFT}
        y2={CHART_BOTTOM - yAxisHeight}
        stroke={AXIS_COLOR}
        strokeWidth={1.5}
        opacity={axisOpacity}
      />

      {/* X-axis */}
      <line
        x1={CHART_LEFT}
        y1={CHART_BOTTOM}
        x2={CHART_LEFT + xAxisWidth}
        y2={CHART_BOTTOM}
        stroke={AXIS_COLOR}
        strokeWidth={1.5}
        opacity={axisOpacity}
      />

      {/* Y-axis label */}
      <text
        x={40}
        y={CHART_TOP + CHART_HEIGHT / 2}
        fill={AXIS_LABEL_COLOR}
        opacity={0.6 * axisOpacity}
        fontSize={14}
        fontFamily="Inter, sans-serif"
        fontWeight={400}
        textAnchor="middle"
        transform={`rotate(-90, 40, ${CHART_TOP + CHART_HEIGHT / 2})`}
      >
        Cost (Developer Hours)
      </text>

      {/* Y-axis tick labels */}
      {Array.from({ length: Y_TICK_COUNT + 1 }).map((_, i) => {
        const val = i / Y_TICK_COUNT;
        const y = CHART_BOTTOM - val * CHART_HEIGHT;
        return (
          <text
            key={`y-label-${i}`}
            x={CHART_LEFT - 16}
            y={y + 4}
            fill={AXIS_LABEL_COLOR}
            opacity={0.6 * axisOpacity}
            fontSize={12}
            fontFamily="Inter, sans-serif"
            fontWeight={400}
            textAnchor="end"
          >
            {val.toFixed(1)}
          </text>
        );
      })}

      {/* X-axis tick labels */}
      {X_TICK_YEARS.map((year) => {
        const x = mapX(year);
        const tickVisible = x <= CHART_LEFT + xAxisWidth ? 1 : 0;
        return (
          <g key={`x-tick-${year}`} opacity={tickVisible * axisOpacity}>
            <line
              x1={x}
              y1={CHART_BOTTOM}
              x2={x}
              y2={CHART_BOTTOM + 6}
              stroke={AXIS_COLOR}
              strokeWidth={1}
            />
            <text
              x={x}
              y={CHART_BOTTOM + 28}
              fill={AXIS_LABEL_COLOR}
              opacity={0.6}
              fontSize={14}
              fontFamily="Inter, sans-serif"
              fontWeight={400}
              textAnchor="middle"
            >
              {year}
            </text>
          </g>
        );
      })}
    </svg>
  );
};

export default ChartAxes;
