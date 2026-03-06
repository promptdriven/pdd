import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  CHART_X,
  CHART_Y,
  CHART_W,
  CHART_H,
  AXIS_COLOR,
  AXIS_TITLE_COLOR,
  GRID_COLOR,
  TIME_MARKER_COLOR,
  AXES_FADE_END,
  GRID_FADE_START,
  GRID_FADE_END,
  GRID_FRACTIONS,
  TIME_MARKERS,
  X_TICKS,
} from "./constants";

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  const axesOpacity = interpolate(frame, [0, AXES_FADE_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  const gridOpacity = interpolate(
    frame,
    [GRID_FADE_START, GRID_FADE_END],
    [0, 0.15],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const timeMarkerOpacity = interpolate(
    frame,
    [GRID_FADE_START, GRID_FADE_END],
    [0, 0.1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Horizontal grid lines at 25%, 50%, 75% */}
        {GRID_FRACTIONS.map((frac) => {
          const y = CHART_Y + CHART_H * (1 - frac);
          return (
            <line
              key={`hgrid-${frac}`}
              x1={CHART_X}
              y1={y}
              x2={CHART_X + CHART_W}
              y2={y}
              stroke={GRID_COLOR}
              strokeWidth={1}
              strokeDasharray="6 4"
              opacity={gridOpacity}
            />
          );
        })}

        {/* Vertical time markers at Month 6, 12, 18 */}
        {TIME_MARKERS.map((tm) => {
          const x = CHART_X + tm.frac * CHART_W;
          return (
            <g key={`tm-${tm.label}`}>
              <line
                x1={x}
                y1={CHART_Y}
                x2={x}
                y2={CHART_Y + CHART_H}
                stroke={GRID_COLOR}
                strokeWidth={1}
                strokeDasharray="6 4"
                opacity={timeMarkerOpacity}
              />
              <text
                x={x}
                y={CHART_Y + CHART_H + 30}
                fill={TIME_MARKER_COLOR}
                fontSize={14}
                fontFamily="Inter, sans-serif"
                fontWeight={400}
                textAnchor="middle"
                opacity={axesOpacity}
              >
                {tm.label}
              </text>
            </g>
          );
        })}

        {/* Y-axis */}
        <line
          x1={CHART_X}
          y1={CHART_Y}
          x2={CHART_X}
          y2={CHART_Y + CHART_H}
          stroke={AXIS_COLOR}
          strokeWidth={2}
          opacity={axesOpacity}
        />

        {/* X-axis */}
        <line
          x1={CHART_X}
          y1={CHART_Y + CHART_H}
          x2={CHART_X + CHART_W}
          y2={CHART_Y + CHART_H}
          stroke={AXIS_COLOR}
          strokeWidth={2}
          opacity={axesOpacity}
        />

        {/* X-axis tick marks */}
        {X_TICKS.map((t) => {
          const x = CHART_X + t * CHART_W;
          return (
            <line
              key={`xtick-${t}`}
              x1={x}
              y1={CHART_Y + CHART_H}
              x2={x}
              y2={CHART_Y + CHART_H + 8}
              stroke={AXIS_COLOR}
              strokeWidth={1.5}
              opacity={axesOpacity}
            />
          );
        })}

        {/* Y-axis tick marks */}
        {GRID_FRACTIONS.map((frac) => {
          const y = CHART_Y + CHART_H * (1 - frac);
          return (
            <line
              key={`ytick-${frac}`}
              x1={CHART_X - 8}
              y1={y}
              x2={CHART_X}
              y2={y}
              stroke={AXIS_COLOR}
              strokeWidth={1.5}
              opacity={axesOpacity}
            />
          );
        })}

        {/* X-axis endpoint labels */}
        <text
          x={CHART_X}
          y={CHART_Y + CHART_H + 30}
          fill={AXIS_COLOR}
          fontSize={18}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="start"
          opacity={axesOpacity}
        >
          Month 1
        </text>
        <text
          x={CHART_X + CHART_W}
          y={CHART_Y + CHART_H + 30}
          fill={AXIS_COLOR}
          fontSize={18}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="end"
          opacity={axesOpacity}
        >
          Month 24
        </text>

        {/* X-axis title */}
        <text
          x={CHART_X + CHART_W / 2}
          y={CHART_Y + CHART_H + 65}
          fill={AXIS_TITLE_COLOR}
          fontSize={20}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="middle"
          opacity={axesOpacity}
        >
          Time
        </text>

        {/* Y-axis title (rotated 90 degrees) */}
        <text
          x={CHART_X - 70}
          y={CHART_Y + CHART_H / 2}
          fill={AXIS_TITLE_COLOR}
          fontSize={20}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="middle"
          transform={`rotate(-90, ${CHART_X - 70}, ${CHART_Y + CHART_H / 2})`}
          opacity={axesOpacity}
        >
          Accumulated Technical Debt
        </text>

        {/* Y-axis endpoint labels */}
        <text
          x={CHART_X - 16}
          y={CHART_Y + CHART_H + 4}
          fill={AXIS_COLOR}
          fontSize={16}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="end"
          opacity={axesOpacity}
        >
          Zero
        </text>
        <text
          x={CHART_X - 16}
          y={CHART_Y + 5}
          fill={AXIS_COLOR}
          fontSize={16}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="end"
          opacity={axesOpacity}
        >
          Critical
        </text>
      </svg>
    </AbsoluteFill>
  );
};

export default ChartAxes;
