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
  GRID_COLOR,
  X_MIN,
  X_MAX,
  Y_MAX,
  Y_HOUR_MAX,
  mapX,
  mapY,
  CHART_APPEAR_END,
} from "./constants";

const YEAR_TICKS = [2014, 2016, 2018, 2020, 2022, 2024, 2026];
const Y_TICKS = [0, 0.25, 0.5, 0.75, 1.0];
const Y_LABELS = ["0h", "5h", "10h", "15h", "20h"];

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  const axisOpacity = interpolate(frame, [0, 30], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  const gridOpacity = interpolate(frame, [10, 40], [0, 0.4], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  const labelOpacity = interpolate(frame, [20, 50], [0, 0.85], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Title */}
      <text
        x={960}
        y={60}
        textAnchor="middle"
        fill="#E2E8F0"
        fontSize={22}
        fontFamily="Inter, sans-serif"
        fontWeight={600}
        opacity={labelOpacity}
      >
        Code Cost: Generate vs. Patch
      </text>

      {/* Y-axis label */}
      <text
        x={40}
        y={(CHART_TOP + CHART_BOTTOM) / 2}
        textAnchor="middle"
        fill={AXIS_LABEL_COLOR}
        fontSize={14}
        fontFamily="Inter, sans-serif"
        fontWeight={400}
        opacity={labelOpacity}
        transform={`rotate(-90, 40, ${(CHART_TOP + CHART_BOTTOM) / 2})`}
      >
        Developer Hours per Feature
      </text>

      {/* Horizontal grid lines */}
      {Y_TICKS.map((yVal, i) => (
        <line
          key={`grid-h-${i}`}
          x1={CHART_LEFT}
          y1={mapY(yVal)}
          x2={CHART_RIGHT}
          y2={mapY(yVal)}
          stroke={GRID_COLOR}
          strokeWidth={1}
          opacity={gridOpacity}
        />
      ))}

      {/* Vertical grid lines */}
      {YEAR_TICKS.map((year, i) => (
        <line
          key={`grid-v-${i}`}
          x1={mapX(year)}
          y1={CHART_TOP}
          x2={mapX(year)}
          y2={CHART_BOTTOM}
          stroke={GRID_COLOR}
          strokeWidth={1}
          opacity={gridOpacity}
        />
      ))}

      {/* X-axis */}
      <line
        x1={CHART_LEFT}
        y1={CHART_BOTTOM}
        x2={CHART_RIGHT}
        y2={CHART_BOTTOM}
        stroke={AXIS_COLOR}
        strokeWidth={2}
        opacity={axisOpacity}
      />

      {/* Y-axis */}
      <line
        x1={CHART_LEFT}
        y1={CHART_TOP}
        x2={CHART_LEFT}
        y2={CHART_BOTTOM}
        stroke={AXIS_COLOR}
        strokeWidth={2}
        opacity={axisOpacity}
      />

      {/* X-axis tick labels */}
      {YEAR_TICKS.map((year, i) => (
        <text
          key={`x-label-${i}`}
          x={mapX(year)}
          y={CHART_BOTTOM + 30}
          textAnchor="middle"
          fill={AXIS_LABEL_COLOR}
          fontSize={13}
          fontFamily="Inter, sans-serif"
          opacity={labelOpacity}
        >
          {year}
        </text>
      ))}

      {/* Y-axis tick labels */}
      {Y_TICKS.map((yVal, i) => (
        <text
          key={`y-label-${i}`}
          x={CHART_LEFT - 16}
          y={mapY(yVal) + 4}
          textAnchor="end"
          fill={AXIS_LABEL_COLOR}
          fontSize={13}
          fontFamily="Inter, sans-serif"
          opacity={labelOpacity}
        >
          {Y_LABELS[i]}
        </text>
      ))}
    </svg>
  );
};

export default ChartAxes;
