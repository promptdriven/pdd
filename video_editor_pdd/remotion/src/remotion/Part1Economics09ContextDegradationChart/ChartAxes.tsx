import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  CHART_X,
  CHART_Y,
  CHART_W,
  CHART_H,
  BARS_START_X,
  BAR_WIDTH,
  BAR_GAP,
  AXIS_COLOR,
  AXIS_TITLE_COLOR,
  GRID_COLOR,
  AXES_FADE_END,
  Y_TICKS,
  BARS,
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
        {Y_TICKS.filter((v) => v > 0).map((val) => {
          const y = CHART_Y + CHART_H * (1 - val / 100);
          return (
            <line
              key={`grid-${val}`}
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

        {/* Y-axis tick marks + labels */}
        {Y_TICKS.map((val) => {
          const y = CHART_Y + CHART_H * (1 - val / 100);
          return (
            <g key={`ytick-${val}`} opacity={axesOpacity}>
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
                {val}%
              </text>
            </g>
          );
        })}

        {/* X-axis tick labels (centered under each bar position) */}
        {BARS.map((bar, i) => {
          const barCenterX =
            BARS_START_X + i * (BAR_WIDTH + BAR_GAP) + BAR_WIDTH / 2;
          return (
            <g key={`xtick-${bar.fillLevel}`} opacity={axesOpacity}>
              <line
                x1={barCenterX}
                y1={CHART_Y + CHART_H}
                x2={barCenterX}
                y2={CHART_Y + CHART_H + 8}
                stroke={AXIS_COLOR}
                strokeWidth={1.5}
              />
              <text
                x={barCenterX}
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
          x={CHART_X - 80}
          y={CHART_Y + CHART_H / 2}
          fill={AXIS_TITLE_COLOR}
          fontSize={20}
          fontFamily="Inter, sans-serif"
          fontWeight={500}
          textAnchor="middle"
          transform={`rotate(-90, ${CHART_X - 80}, ${CHART_Y + CHART_H / 2})`}
          opacity={axesOpacity}
        >
          AI Capability
        </text>
      </svg>
    </AbsoluteFill>
  );
};

export default ChartAxes;
