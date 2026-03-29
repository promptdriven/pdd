import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  AXIS_COLOR,
  AXIS_LABEL_COLOR,
  AXIS_LABEL_OPACITY,
  AXIS_STROKE_WIDTH,
  GRID_COLOR,
  GRID_OPACITY,
  FONT_FAMILY,
  AXIS_FONT_SIZE,
  X_MIN,
  X_MAX,
  X_TICK_INTERVAL,
  AXES_START,
  AXES_END,
} from "./constants";

const GRID_LINE_COUNT = 5; // horizontal grid lines

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  // Axes draw-in progress (0→1 over frames 0-30)
  const axisProgress = interpolate(frame, [AXES_START, AXES_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  // Grid fade-in slightly behind axis draw
  const gridOpacity = interpolate(frame, [10, AXES_END], [0, GRID_OPACITY], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Label fade-in
  const labelOpacity = interpolate(
    frame,
    [AXES_END - 10, AXES_END + 5],
    [0, AXIS_LABEL_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // X-axis decade ticks
  const xTicks: number[] = [];
  for (let year = X_MIN; year <= X_MAX; year += X_TICK_INTERVAL) {
    xTicks.push(year);
  }

  // Horizontal grid lines (evenly spaced in chart area)
  const gridYPositions: number[] = [];
  for (let i = 1; i <= GRID_LINE_COUNT; i++) {
    gridYPositions.push(
      CHART_TOP + (i / (GRID_LINE_COUNT + 1)) * CHART_HEIGHT
    );
  }

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Horizontal grid lines */}
      {gridYPositions.map((y, i) => (
        <line
          key={`grid-h-${i}`}
          x1={CHART_LEFT}
          y1={y}
          x2={CHART_RIGHT}
          y2={y}
          stroke={GRID_COLOR}
          strokeWidth={1}
          opacity={gridOpacity}
        />
      ))}

      {/* X-axis line (draws left to right) */}
      <line
        x1={CHART_LEFT}
        y1={CHART_BOTTOM}
        x2={CHART_LEFT + CHART_WIDTH * axisProgress}
        y2={CHART_BOTTOM}
        stroke={AXIS_COLOR}
        strokeWidth={AXIS_STROKE_WIDTH}
      />

      {/* Y-axis line (draws bottom to top) */}
      <line
        x1={CHART_LEFT}
        y1={CHART_BOTTOM}
        x2={CHART_LEFT}
        y2={CHART_BOTTOM - CHART_HEIGHT * axisProgress}
        stroke={AXIS_COLOR}
        strokeWidth={AXIS_STROKE_WIDTH}
      />

      {/* X-axis tick marks and labels */}
      {xTicks.map((year) => {
        const tickX =
          CHART_LEFT + ((year - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;
        const tickProgress = interpolate(
          axisProgress,
          [
            Math.max(0, (year - X_MIN) / (X_MAX - X_MIN) - 0.05),
            Math.min(1, (year - X_MIN) / (X_MAX - X_MIN) + 0.05),
          ],
          [0, 1],
          { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
        );

        return (
          <g key={`xtick-${year}`} opacity={tickProgress}>
            <line
              x1={tickX}
              y1={CHART_BOTTOM}
              x2={tickX}
              y2={CHART_BOTTOM + 8}
              stroke={AXIS_COLOR}
              strokeWidth={1}
            />
            <text
              x={tickX}
              y={CHART_BOTTOM + 30}
              textAnchor="middle"
              fill={AXIS_LABEL_COLOR}
              opacity={labelOpacity / AXIS_LABEL_OPACITY}
              fontFamily={FONT_FAMILY}
              fontSize={AXIS_FONT_SIZE}
              fontWeight={400}
            >
              {year}
            </text>
          </g>
        );
      })}

      {/* Y-axis label */}
      <text
        x={CHART_LEFT - 50}
        y={CHART_TOP + CHART_HEIGHT / 2}
        textAnchor="middle"
        fill={AXIS_LABEL_COLOR}
        opacity={labelOpacity}
        fontFamily={FONT_FAMILY}
        fontSize={AXIS_FONT_SIZE}
        fontWeight={400}
        transform={`rotate(-90, ${CHART_LEFT - 50}, ${CHART_TOP + CHART_HEIGHT / 2})`}
      >
        Cost (relative to hourly wage)
      </text>

      {/* Y-axis tick labels: 0.0, 0.2, 0.4, 0.6, 0.8, 1.0 */}
      {[0, 0.2, 0.4, 0.6, 0.8, 1.0].map((val) => {
        const tickY = CHART_BOTTOM - (val / 1) * CHART_HEIGHT;
        return (
          <text
            key={`ytick-${val}`}
            x={CHART_LEFT - 16}
            y={tickY + 4}
            textAnchor="end"
            fill={AXIS_LABEL_COLOR}
            opacity={labelOpacity}
            fontFamily={FONT_FAMILY}
            fontSize={AXIS_FONT_SIZE - 1}
            fontWeight={400}
          >
            {val.toFixed(1)}
          </text>
        );
      })}
    </svg>
  );
};

export default ChartAxes;
