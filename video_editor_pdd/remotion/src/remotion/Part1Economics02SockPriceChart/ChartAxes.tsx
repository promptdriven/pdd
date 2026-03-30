import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN,
  X_MAX,
  X_TICK_INTERVAL,
  AXIS_COLOR,
  AXIS_LABEL_COLOR,
  GRID_COLOR,
  GRID_OPACITY,
  FONT_FAMILY,
  AXIS_FONT_SIZE,
  AXIS_LABEL_OPACITY,
  AXES_START,
  AXES_END,
  xToPixel,
} from "./constants";

/**
 * Draws the chart axes, grid lines, tick labels, and axis titles.
 * Animates in during AXES_START → AXES_END.
 */
export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  // Overall draw-in progress (0 → 1)
  const drawProgress = interpolate(frame, [AXES_START, AXES_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  // Grid fade-in slightly behind axes
  const gridOpacity = interpolate(frame, [AXES_START + 5, AXES_END], [0, GRID_OPACITY], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Generate x-axis tick years
  const xTicks: number[] = [];
  for (let year = X_MIN; year <= X_MAX; year += X_TICK_INTERVAL) {
    xTicks.push(year);
  }

  // Horizontal grid lines (5 evenly spaced across chart height)
  const gridLineCount = 5;
  const gridLines: number[] = [];
  for (let i = 0; i <= gridLineCount; i++) {
    gridLines.push(CHART_TOP + (i / gridLineCount) * CHART_HEIGHT);
  }

  return (
    <div style={{ position: "absolute", inset: 0 }}>
      {/* Horizontal grid lines */}
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {gridLines.map((y, i) => (
          <line
            key={`grid-h-${i}`}
            x1={CHART_LEFT}
            y1={y}
            x2={CHART_LEFT + CHART_WIDTH * drawProgress}
            y2={y}
            stroke={GRID_COLOR}
            strokeWidth={1}
            opacity={gridOpacity}
          />
        ))}

        {/* X-axis line */}
        <line
          x1={CHART_LEFT}
          y1={CHART_BOTTOM}
          x2={CHART_LEFT + CHART_WIDTH * drawProgress}
          y2={CHART_BOTTOM}
          stroke={AXIS_COLOR}
          strokeWidth={1.5}
          opacity={drawProgress}
        />

        {/* Y-axis line */}
        <line
          x1={CHART_LEFT}
          y1={CHART_BOTTOM}
          x2={CHART_LEFT}
          y2={CHART_BOTTOM - CHART_HEIGHT * drawProgress}
          stroke={AXIS_COLOR}
          strokeWidth={1.5}
          opacity={drawProgress}
        />

        {/* X-axis tick marks and labels */}
        {xTicks.map((year) => {
          const px = xToPixel(year);
          const tickProgress = interpolate(
            drawProgress,
            [Math.max(0, (year - X_MIN) / (X_MAX - X_MIN) - 0.1), Math.min(1, (year - X_MIN) / (X_MAX - X_MIN) + 0.1)],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          );
          return (
            <g key={`xtick-${year}`} opacity={tickProgress}>
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
                textAnchor="middle"
                fill={AXIS_LABEL_COLOR}
                fontSize={AXIS_FONT_SIZE}
                fontFamily={FONT_FAMILY}
                fontWeight={400}
                opacity={AXIS_LABEL_OPACITY}
              >
                {year}
              </text>
            </g>
          );
        })}

        {/* Y-axis tick marks (0.0, 0.2, 0.4, 0.6, 0.8, 1.0) */}
        {[0, 0.2, 0.4, 0.6, 0.8, 1.0].map((val) => {
          const py = CHART_BOTTOM - val * CHART_HEIGHT;
          const tickProgress = interpolate(
            drawProgress,
            [Math.max(0, val - 0.15), Math.min(1, val + 0.15)],
            [0, 1],
            { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
          );
          return (
            <g key={`ytick-${val}`} opacity={tickProgress}>
              <line
                x1={CHART_LEFT - 8}
                y1={py}
                x2={CHART_LEFT}
                y2={py}
                stroke={AXIS_COLOR}
                strokeWidth={1}
              />
              <text
                x={CHART_LEFT - 14}
                y={py + 5}
                textAnchor="end"
                fill={AXIS_LABEL_COLOR}
                fontSize={AXIS_FONT_SIZE}
                fontFamily={FONT_FAMILY}
                fontWeight={400}
                opacity={AXIS_LABEL_OPACITY}
              >
                {val.toFixed(1)}
              </text>
            </g>
          );
        })}
      </svg>

      {/* Y-axis title (rotated) */}
      <div
        style={{
          position: "absolute",
          left: 30,
          top: CHART_TOP + CHART_HEIGHT / 2,
          transform: "rotate(-90deg)",
          transformOrigin: "center center",
          color: AXIS_LABEL_COLOR,
          fontFamily: FONT_FAMILY,
          fontSize: AXIS_FONT_SIZE,
          fontWeight: 400,
          opacity: AXIS_LABEL_OPACITY * drawProgress,
          whiteSpace: "nowrap",
        }}
      >
        Cost (relative to hourly wage)
      </div>

      {/* X-axis title */}
      <div
        style={{
          position: "absolute",
          left: CHART_LEFT + CHART_WIDTH / 2,
          top: CHART_BOTTOM + 50,
          transform: "translateX(-50%)",
          color: AXIS_LABEL_COLOR,
          fontFamily: FONT_FAMILY,
          fontSize: AXIS_FONT_SIZE,
          fontWeight: 400,
          opacity: AXIS_LABEL_OPACITY * drawProgress,
          whiteSpace: "nowrap",
        }}
      >
        Year
      </div>
    </div>
  );
};

export default ChartAxes;
