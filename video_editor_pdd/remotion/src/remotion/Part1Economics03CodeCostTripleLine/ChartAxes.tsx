import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  CHART_W,
  CHART_H,
  MARGIN,
  AXIS_COLOR,
  LABEL_COLOR,
  GRID_COLOR,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
  Y_MAJOR,
  MORPH_END,
  xToPixel,
  yToPixel,
} from "./constants";

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  // Morph-in opacity for the axis system (visible from frame 0 but labels transition)
  const axisOpacity = interpolate(frame, [0, MORPH_END], [0.5, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.ease),
  });

  // X-axis ticks: every year (minor), label every 2 years (major)
  const xTicks: number[] = [];
  for (let yr = X_MIN; yr <= X_MAX; yr++) {
    xTicks.push(yr);
  }

  // Y-axis major ticks
  const yTicks: number[] = [];
  for (let val = Y_MIN; val <= Y_MAX; val += Y_MAJOR) {
    yTicks.push(val);
  }

  // Y-axis minor grid (every 5)
  const yGridLines: number[] = [];
  for (let val = Y_MIN + Y_MAJOR; val <= Y_MAX; val += Y_MAJOR) {
    yGridLines.push(val);
  }

  return (
    <div
      style={{
        position: "absolute",
        left: MARGIN.left,
        top: MARGIN.top,
        width: CHART_W,
        height: CHART_H,
        opacity: axisOpacity,
      }}
    >
      <svg
        width={CHART_W}
        height={CHART_H}
        viewBox={`0 0 ${CHART_W} ${CHART_H}`}
        style={{ overflow: "visible" }}
      >
        {/* Horizontal grid lines (dashed) */}
        {yGridLines.map((val) => {
          const py = yToPixel(val);
          return (
            <line
              key={`grid-${val}`}
              x1={0}
              y1={py}
              x2={CHART_W}
              y2={py}
              stroke={GRID_COLOR}
              strokeOpacity={0.08}
              strokeWidth={1}
              strokeDasharray="6 4"
            />
          );
        })}

        {/* X-axis line */}
        <line
          x1={0}
          y1={CHART_H}
          x2={CHART_W}
          y2={CHART_H}
          stroke={AXIS_COLOR}
          strokeOpacity={0.25}
          strokeWidth={1}
        />

        {/* Y-axis line */}
        <line
          x1={0}
          y1={0}
          x2={0}
          y2={CHART_H}
          stroke={AXIS_COLOR}
          strokeOpacity={0.25}
          strokeWidth={1}
        />

        {/* X-axis ticks and labels */}
        {xTicks.map((yr) => {
          const px = xToPixel(yr);
          const isMajor = (yr - X_MIN) % 2 === 0;
          const tickLen = isMajor ? 8 : 4;
          return (
            <g key={`xtick-${yr}`}>
              <line
                x1={px}
                y1={CHART_H}
                x2={px}
                y2={CHART_H + tickLen}
                stroke={AXIS_COLOR}
                strokeOpacity={0.25}
                strokeWidth={1}
              />
              {isMajor && (
                <text
                  x={px}
                  y={CHART_H + 28}
                  textAnchor="middle"
                  fill={LABEL_COLOR}
                  fillOpacity={0.25}
                  fontFamily="Inter, sans-serif"
                  fontSize={10}
                >
                  {yr}
                </text>
              )}
            </g>
          );
        })}

        {/* Y-axis ticks and labels */}
        {yTicks.map((val) => {
          const py = yToPixel(val);
          return (
            <g key={`ytick-${val}`}>
              <line
                x1={-8}
                y1={py}
                x2={0}
                y2={py}
                stroke={AXIS_COLOR}
                strokeOpacity={0.25}
                strokeWidth={1}
              />
              <text
                x={-16}
                y={py + 4}
                textAnchor="end"
                fill={LABEL_COLOR}
                fillOpacity={0.25}
                fontFamily="Inter, sans-serif"
                fontSize={10}
              >
                {val}
              </text>
            </g>
          );
        })}

        {/* X-axis label */}
        <text
          x={CHART_W / 2}
          y={CHART_H + 60}
          textAnchor="middle"
          fill={LABEL_COLOR}
          fillOpacity={0.3}
          fontFamily="Inter, sans-serif"
          fontSize={12}
        >
          Year
        </text>

        {/* Y-axis label (rotated) */}
        <text
          x={-CHART_H / 2}
          y={-60}
          textAnchor="middle"
          fill={LABEL_COLOR}
          fillOpacity={0.3}
          fontFamily="Inter, sans-serif"
          fontSize={12}
          transform="rotate(-90)"
        >
          Cost (Developer Hours)
        </text>
      </svg>
    </div>
  );
};
