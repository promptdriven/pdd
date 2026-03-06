import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";

const CHART_X = 300;
const CHART_Y = 150;
const CHART_W = 1320;
const CHART_H = 700;
const AXIS_COLOR = "#94A3B8";
const AXIS_TITLE_COLOR = "#CBD5E1";
const GRID_COLOR = "#334155";

const BAR_WIDTH = 120;
const BAR_GAP = 60;
const NUM_BARS = 5;
const TOTAL_BARS_WIDTH = NUM_BARS * BAR_WIDTH + (NUM_BARS - 1) * BAR_GAP;
const BARS_START_X = CHART_X + (CHART_W - TOTAL_BARS_WIDTH) / 2;

const X_LABELS = ["10%", "25%", "50%", "75%", "100%"];
const Y_TICKS = [0, 25, 50, 75, 100];

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  const axesOpacity = interpolate(frame, [0, 30], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
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
        {X_LABELS.map((label, i) => {
          const barCenterX = BARS_START_X + i * (BAR_WIDTH + BAR_GAP) + BAR_WIDTH / 2;
          return (
            <g key={`xtick-${label}`} opacity={axesOpacity}>
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
                {label}
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
