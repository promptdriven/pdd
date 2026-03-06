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
  AXES_FADE_END,
  Y_GRID_FRACTIONS,
  BARS,
  BAR_POSITIONS,
  BAR_WIDTH,
} from "./constants";

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  const axesOpacity = interpolate(frame, [0, AXES_FADE_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Horizontal grid lines */}
        {Y_GRID_FRACTIONS.map((frac) => {
          const y = CHART_Y + CHART_H * (1 - frac);
          return (
            <line
              key={`grid-${frac}`}
              x1={CHART_X}
              y1={y}
              x2={CHART_X + CHART_W}
              y2={y}
              stroke={GRID_COLOR}
              strokeWidth={1}
              strokeDasharray="6 4"
              opacity={axesOpacity * 0.3}
            />
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

        {/* Y-axis tick marks and labels */}
        {Y_GRID_FRACTIONS.map((frac) => {
          const y = CHART_Y + CHART_H * (1 - frac);
          return (
            <g key={`ytick-${frac}`} opacity={axesOpacity}>
              <line
                x1={CHART_X - 8}
                y1={y}
                x2={CHART_X}
                y2={y}
                stroke={AXIS_COLOR}
                strokeWidth={1.5}
              />
              <text
                x={CHART_X - 16}
                y={y + 5}
                fill={AXIS_COLOR}
                fontSize={16}
                fontFamily="Inter, sans-serif"
                fontWeight={500}
                textAnchor="end"
              >
                {`${Math.round(frac * 100)}%`}
              </text>
            </g>
          );
        })}

        {/* 0% label at baseline */}
        <text
          x={CHART_X - 16}
          y={CHART_Y + CHART_H + 5}
          fill={AXIS_COLOR}
          fontSize={16}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="end"
          opacity={axesOpacity}
        >
          0%
        </text>

        {/* X-axis tick marks and labels (centered under each bar) */}
        {BARS.map((bar, i) => {
          const x = BAR_POSITIONS[i] + BAR_WIDTH / 2;
          return (
            <g key={`xtick-${i}`} opacity={axesOpacity}>
              <line
                x1={x}
                y1={CHART_Y + CHART_H}
                x2={x}
                y2={CHART_Y + CHART_H + 8}
                stroke={AXIS_COLOR}
                strokeWidth={1.5}
              />
              <text
                x={x}
                y={CHART_Y + CHART_H + 32}
                fill={AXIS_COLOR}
                fontSize={18}
                fontFamily="Inter, sans-serif"
                fontWeight={500}
                textAnchor="middle"
              >
                {bar.fillLevel}
              </text>
            </g>
          );
        })}

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
          Context Window Fill Level
        </text>

        {/* Y-axis title (rotated) */}
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
          AI Capability
        </text>
      </svg>
    </AbsoluteFill>
  );
};

export default ChartAxes;
