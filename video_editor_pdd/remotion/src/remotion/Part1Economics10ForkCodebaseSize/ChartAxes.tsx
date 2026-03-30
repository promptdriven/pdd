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
  FONT_FAMILY,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
  xToPixel,
  yToPixel,
  CHART_APPEAR_END,
} from "./constants";

const X_TICKS = [2014, 2016, 2018, 2020, 2022, 2024, 2026];
const Y_TICKS = [0, 0.2, 0.4, 0.6, 0.8, 1.0];
const Y_LABELS = ["0", "0.2", "0.4", "0.6", "0.8", "1.0"];

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  const axisOpacity = interpolate(frame, [0, 30], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, opacity: axisOpacity }}
    >
      {/* Grid lines */}
      {Y_TICKS.map((tick) => {
        const py = yToPixel(tick);
        return (
          <line
            key={`grid-y-${tick}`}
            x1={CHART_LEFT}
            y1={py}
            x2={CHART_RIGHT}
            y2={py}
            stroke={GRID_COLOR}
            strokeWidth={1}
          />
        );
      })}

      {/* X axis */}
      <line
        x1={CHART_LEFT}
        y1={CHART_BOTTOM}
        x2={CHART_RIGHT}
        y2={CHART_BOTTOM}
        stroke={AXIS_COLOR}
        strokeWidth={2}
      />

      {/* Y axis */}
      <line
        x1={CHART_LEFT}
        y1={CHART_TOP}
        x2={CHART_LEFT}
        y2={CHART_BOTTOM}
        stroke={AXIS_COLOR}
        strokeWidth={2}
      />

      {/* X tick labels */}
      {X_TICKS.map((tick) => {
        const px = xToPixel(tick);
        return (
          <text
            key={`x-label-${tick}`}
            x={px}
            y={CHART_BOTTOM + 36}
            textAnchor="middle"
            fill={AXIS_LABEL_COLOR}
            fontSize={14}
            fontFamily={FONT_FAMILY}
            fontWeight={400}
          >
            {tick}
          </text>
        );
      })}

      {/* Y tick labels */}
      {Y_TICKS.map((tick, i) => {
        const py = yToPixel(tick);
        return (
          <text
            key={`y-label-${tick}`}
            x={CHART_LEFT - 16}
            y={py + 5}
            textAnchor="end"
            fill={AXIS_LABEL_COLOR}
            fontSize={13}
            fontFamily={FONT_FAMILY}
            fontWeight={400}
          >
            {Y_LABELS[i]}
          </text>
        );
      })}

      {/* Y axis label */}
      <text
        x={50}
        y={(CHART_TOP + CHART_BOTTOM) / 2}
        textAnchor="middle"
        fill={AXIS_LABEL_COLOR}
        fontSize={14}
        fontFamily={FONT_FAMILY}
        fontWeight={500}
        transform={`rotate(-90, 50, ${(CHART_TOP + CHART_BOTTOM) / 2})`}
      >
        Cost per feature (developer-hours, normalized)
      </text>

      {/* X axis label */}
      <text
        x={(CHART_LEFT + CHART_RIGHT) / 2}
        y={CHART_BOTTOM + 66}
        textAnchor="middle"
        fill={AXIS_LABEL_COLOR}
        fontSize={14}
        fontFamily={FONT_FAMILY}
        fontWeight={500}
      >
        Year
      </text>
    </svg>
  );
};

export default ChartAxes;
