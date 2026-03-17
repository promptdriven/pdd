import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  MARGIN_LEFT,
  MARGIN_TOP,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
  X_MAJOR_INTERVAL,
  X_MINOR_INTERVAL,
  Y_MAJOR_INTERVAL,
  AXIS_COLOR,
  AXIS_OPACITY,
  GRID_COLOR,
  GRID_OPACITY,
  LABEL_COLOR,
  AXIS_LABEL_SIZE,
  TICK_LABEL_SIZE,
  AXES_DRAW_START,
  AXES_DRAW_END,
  GRID_FADE_START,
  GRID_FADE_END,
} from "./constants";

/** Map data x to pixel x */
const xToPixel = (x: number): number =>
  MARGIN_LEFT + ((x - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;

/** Map data y to pixel y (inverted: higher y = higher on screen) */
const yToPixel = (y: number): number =>
  MARGIN_TOP + CHART_HEIGHT - ((y - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  const axisProgress = interpolate(
    frame,
    [AXES_DRAW_START, AXES_DRAW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.cubic) }
  );

  const gridOpacity = interpolate(
    frame,
    [GRID_FADE_START, GRID_FADE_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.out(Easing.quad) }
  );

  // X-axis origin and extent
  const xAxisY = yToPixel(Y_MIN);
  const xAxisEndX = MARGIN_LEFT + CHART_WIDTH * axisProgress;

  // Y-axis origin and extent
  const yAxisX = MARGIN_LEFT;
  const yAxisStartY = yToPixel(Y_MIN);
  const yAxisEndY = yToPixel(Y_MIN) - CHART_HEIGHT * axisProgress;

  // Build major x ticks
  const xMajorTicks: number[] = [];
  for (let x = X_MIN; x <= X_MAX; x += X_MAJOR_INTERVAL) {
    xMajorTicks.push(x);
  }

  // Build minor x ticks
  const xMinorTicks: number[] = [];
  for (let x = X_MIN; x <= X_MAX; x += X_MINOR_INTERVAL) {
    if (x % X_MAJOR_INTERVAL !== 0) {
      xMinorTicks.push(x);
    }
  }

  // Build y ticks
  const yMajorTicks: number[] = [];
  for (let y = Y_MIN; y <= Y_MAX; y += Y_MAJOR_INTERVAL) {
    yMajorTicks.push(y);
  }

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Horizontal grid lines */}
      {yMajorTicks.map((y) => {
        if (y === Y_MIN) return null; // skip baseline
        const py = yToPixel(y);
        return (
          <line
            key={`grid-y-${y}`}
            x1={MARGIN_LEFT}
            y1={py}
            x2={MARGIN_LEFT + CHART_WIDTH}
            y2={py}
            stroke={GRID_COLOR}
            strokeOpacity={GRID_OPACITY * gridOpacity}
            strokeWidth={1}
            strokeDasharray="6 4"
          />
        );
      })}

      {/* X-axis line */}
      <line
        x1={MARGIN_LEFT}
        y1={xAxisY}
        x2={xAxisEndX}
        y2={xAxisY}
        stroke={AXIS_COLOR}
        strokeOpacity={AXIS_OPACITY}
        strokeWidth={1}
      />

      {/* Y-axis line */}
      <line
        x1={yAxisX}
        y1={yAxisStartY}
        x2={yAxisX}
        y2={yAxisEndY}
        stroke={AXIS_COLOR}
        strokeOpacity={AXIS_OPACITY}
        strokeWidth={1}
      />

      {/* X major ticks + labels */}
      {xMajorTicks.map((x) => {
        const px = xToPixel(x);
        const tickVisible = px <= xAxisEndX ? 1 : 0;
        return (
          <g key={`xtick-${x}`} opacity={tickVisible * axisProgress}>
            <line
              x1={px}
              y1={xAxisY}
              x2={px}
              y2={xAxisY + 8}
              stroke={AXIS_COLOR}
              strokeOpacity={AXIS_OPACITY}
              strokeWidth={1}
            />
            <text
              x={px}
              y={xAxisY + 24}
              textAnchor="middle"
              fill={LABEL_COLOR}
              fillOpacity={0.25}
              fontSize={TICK_LABEL_SIZE}
              fontFamily="'Inter', sans-serif"
            >
              {x}
            </text>
          </g>
        );
      })}

      {/* X minor ticks */}
      {xMinorTicks.map((x) => {
        const px = xToPixel(x);
        const tickVisible = px <= xAxisEndX ? 1 : 0;
        return (
          <line
            key={`xminor-${x}`}
            x1={px}
            y1={xAxisY}
            x2={px}
            y2={xAxisY + 4}
            stroke={AXIS_COLOR}
            strokeOpacity={AXIS_OPACITY * 0.5 * tickVisible * axisProgress}
            strokeWidth={1}
          />
        );
      })}

      {/* Y major ticks + labels */}
      {yMajorTicks.map((y) => {
        const py = yToPixel(y);
        const tickVisible = py >= yAxisEndY ? 1 : 0;
        return (
          <g key={`ytick-${y}`} opacity={tickVisible * axisProgress}>
            <line
              x1={MARGIN_LEFT - 8}
              y1={py}
              x2={MARGIN_LEFT}
              y2={py}
              stroke={AXIS_COLOR}
              strokeOpacity={AXIS_OPACITY}
              strokeWidth={1}
            />
            <text
              x={MARGIN_LEFT - 14}
              y={py + 4}
              textAnchor="end"
              fill={LABEL_COLOR}
              fillOpacity={0.25}
              fontSize={TICK_LABEL_SIZE}
              fontFamily="'Inter', sans-serif"
            >
              {y}%
            </text>
          </g>
        );
      })}

      {/* X-axis label: "Year" */}
      <text
        x={MARGIN_LEFT + CHART_WIDTH / 2}
        y={xAxisY + 60}
        textAnchor="middle"
        fill={LABEL_COLOR}
        fillOpacity={0.3 * axisProgress}
        fontSize={AXIS_LABEL_SIZE}
        fontFamily="'Inter', sans-serif"
      >
        Year
      </text>

      {/* Y-axis label: "Cost (% of hourly wage)" — rotated */}
      <text
        x={MARGIN_LEFT - 70}
        y={MARGIN_TOP + CHART_HEIGHT / 2}
        textAnchor="middle"
        fill={LABEL_COLOR}
        fillOpacity={0.3 * axisProgress}
        fontSize={AXIS_LABEL_SIZE}
        fontFamily="'Inter', sans-serif"
        transform={`rotate(-90, ${MARGIN_LEFT - 70}, ${MARGIN_TOP + CHART_HEIGHT / 2})`}
      >
        Cost (% of hourly wage)
      </text>
    </svg>
  );
};

export default ChartAxes;
