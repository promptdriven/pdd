import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CHART_LEFT,
  CHART_TOP,
  CHART_RIGHT,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  AXIS_COLOR,
  AXIS_LABEL_COLOR,
  AXIS_STROKE_WIDTH,
  GRID_COLOR,
  GRID_OPACITY,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
  AXES_DRAW_START,
  AXES_DRAW_END,
  xToPixel,
} from "./constants";

const DECADE_TICKS = [1950, 1960, 1970, 1980, 1990, 2000, 2010, 2020];
const Y_TICKS = [0, 0.2, 0.4, 0.6, 0.8, 1.0];
const GRID_LINE_COUNT = 5;

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  const axisProgress = interpolate(
    frame,
    [AXES_DRAW_START, AXES_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  const labelOpacity = interpolate(
    frame,
    [AXES_DRAW_START + 10, AXES_DRAW_END],
    [0, 0.6],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  const gridOpacity = interpolate(
    frame,
    [AXES_DRAW_START, AXES_DRAW_END],
    [0, GRID_OPACITY],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Horizontal grid lines */}
      {Array.from({ length: GRID_LINE_COUNT }, (_, i) => {
        const yFrac = (i + 1) / (GRID_LINE_COUNT + 1);
        const yPos = CHART_TOP + yFrac * CHART_HEIGHT;
        return (
          <line
            key={`grid-h-${i}`}
            x1={CHART_LEFT}
            y1={yPos}
            x2={CHART_LEFT + CHART_WIDTH * axisProgress}
            y2={yPos}
            stroke={GRID_COLOR}
            strokeWidth={1}
            opacity={gridOpacity}
          />
        );
      })}

      {/* X-axis line */}
      <line
        x1={CHART_LEFT}
        y1={CHART_BOTTOM}
        x2={CHART_LEFT + CHART_WIDTH * axisProgress}
        y2={CHART_BOTTOM}
        stroke={AXIS_COLOR}
        strokeWidth={AXIS_STROKE_WIDTH}
      />

      {/* Y-axis line */}
      <line
        x1={CHART_LEFT}
        y1={CHART_BOTTOM}
        x2={CHART_LEFT}
        y2={CHART_BOTTOM - CHART_HEIGHT * axisProgress}
        stroke={AXIS_COLOR}
        strokeWidth={AXIS_STROKE_WIDTH}
      />

      {/* X-axis decade labels */}
      {DECADE_TICKS.map((year) => {
        const px = xToPixel(year);
        return (
          <g key={`x-label-${year}`}>
            <line
              x1={px}
              y1={CHART_BOTTOM}
              x2={px}
              y2={CHART_BOTTOM + 8}
              stroke={AXIS_COLOR}
              strokeWidth={1}
              opacity={labelOpacity}
            />
            <text
              x={px}
              y={CHART_BOTTOM + 28}
              textAnchor="middle"
              fill={AXIS_LABEL_COLOR}
              opacity={labelOpacity}
              fontFamily="Inter, sans-serif"
              fontSize={14}
              fontWeight={400}
            >
              {year}
            </text>
          </g>
        );
      })}

      {/* Y-axis tick labels */}
      {Y_TICKS.map((val) => {
        const py =
          CHART_BOTTOM - ((val - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;
        return (
          <g key={`y-label-${val}`}>
            <line
              x1={CHART_LEFT - 6}
              y1={py}
              x2={CHART_LEFT}
              y2={py}
              stroke={AXIS_COLOR}
              strokeWidth={1}
              opacity={labelOpacity}
            />
            <text
              x={CHART_LEFT - 14}
              y={py + 4}
              textAnchor="end"
              fill={AXIS_LABEL_COLOR}
              opacity={labelOpacity}
              fontFamily="Inter, sans-serif"
              fontSize={14}
              fontWeight={400}
            >
              {val.toFixed(1)}
            </text>
          </g>
        );
      })}

      {/* Y-axis label (rotated) */}
      <text
        x={CHART_LEFT - 80}
        y={CHART_TOP + CHART_HEIGHT / 2}
        textAnchor="middle"
        fill={AXIS_LABEL_COLOR}
        opacity={labelOpacity}
        fontFamily="Inter, sans-serif"
        fontSize={14}
        fontWeight={400}
        transform={`rotate(-90, ${CHART_LEFT - 80}, ${CHART_TOP + CHART_HEIGHT / 2})`}
      >
        Cost (relative to hourly wage)
      </text>

      {/* X-axis label */}
      <text
        x={CHART_LEFT + CHART_WIDTH / 2}
        y={CHART_BOTTOM + 55}
        textAnchor="middle"
        fill={AXIS_LABEL_COLOR}
        opacity={labelOpacity}
        fontFamily="Inter, sans-serif"
        fontSize={14}
        fontWeight={400}
      >
        Year
      </text>
    </svg>
  );
};

export default ChartAxes;
