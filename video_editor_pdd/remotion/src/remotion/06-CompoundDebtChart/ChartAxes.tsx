import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";

const WIDTH = 1920;
const HEIGHT = 1080;
const CHART_X = 200;
const CHART_Y = 80;
const CHART_W = 1620;
const CHART_H = 800;
const AXIS_COLOR = "#94A3B8";
const AXIS_TITLE_COLOR = "#CBD5E1";
const GRID_COLOR = "#334155";
const TIME_MARKER_COLOR = "#64748B";
const FONT_FAMILY = "Inter, sans-serif";
const GRID_FRACTIONS = [0.25, 0.5, 0.75];

const TIME_MARKERS = [
  { frac: (6 - 1) / 23, label: "Month 6" },
  { frac: (12 - 1) / 23, label: "Month 12" },
  { frac: (18 - 1) / 23, label: "Month 18" },
];

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  const axesOpacity = interpolate(frame, [0, 30], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.cubic),
  });

  const gridOpacity = interpolate(frame, [20, 50], [0, 0.15], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
  });

  const timeMarkerOpacity = interpolate(frame, [20, 50], [0, 0.1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.out(Easing.quad),
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
        {GRID_FRACTIONS.map((frac) => {
          const y = CHART_Y + CHART_H * (1 - frac);
          return (
            <line
              key={`grid-h-${frac}`}
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

        {/* Vertical time marker lines */}
        {TIME_MARKERS.map((marker) => {
          const x = CHART_X + marker.frac * CHART_W;
          return (
            <g key={`tm-${marker.label}`}>
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
                y={CHART_Y + CHART_H + 36}
                fill={TIME_MARKER_COLOR}
                fontSize={14}
                fontFamily={FONT_FAMILY}
                fontWeight={400}
                textAnchor="middle"
                opacity={axesOpacity}
              >
                {marker.label}
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

        {/* X-axis endpoint labels */}
        <text
          x={CHART_X}
          y={CHART_Y + CHART_H + 36}
          fill={AXIS_COLOR}
          fontSize={18}
          fontFamily={FONT_FAMILY}
          fontWeight={500}
          textAnchor="start"
          opacity={axesOpacity}
        >
          Month 1
        </text>
        <text
          x={CHART_X + CHART_W}
          y={CHART_Y + CHART_H + 36}
          fill={AXIS_COLOR}
          fontSize={18}
          fontFamily={FONT_FAMILY}
          fontWeight={500}
          textAnchor="end"
          opacity={axesOpacity}
        >
          Month 24
        </text>

        {/* X-axis title */}
        <text
          x={CHART_X + CHART_W / 2}
          y={CHART_Y + CHART_H + 70}
          fill={AXIS_TITLE_COLOR}
          fontSize={20}
          fontFamily={FONT_FAMILY}
          fontWeight={500}
          textAnchor="middle"
          opacity={axesOpacity}
        >
          Time
        </text>

        {/* Y-axis title (rotated 90deg) */}
        <text
          x={CHART_X - 70}
          y={CHART_Y + CHART_H / 2}
          fill={AXIS_TITLE_COLOR}
          fontSize={20}
          fontFamily={FONT_FAMILY}
          fontWeight={500}
          textAnchor="middle"
          transform={`rotate(-90, ${CHART_X - 70}, ${CHART_Y + CHART_H / 2})`}
          opacity={axesOpacity}
        >
          Accumulated Technical Debt
        </text>

        {/* Y-axis labels: Zero at bottom, Critical at top */}
        <text
          x={CHART_X - 16}
          y={CHART_Y + CHART_H + 4}
          fill={AXIS_COLOR}
          fontSize={16}
          fontFamily={FONT_FAMILY}
          fontWeight={500}
          textAnchor="end"
          opacity={axesOpacity}
        >
          Zero
        </text>
        <text
          x={CHART_X - 16}
          y={CHART_Y + 6}
          fill={AXIS_COLOR}
          fontSize={16}
          fontFamily={FONT_FAMILY}
          fontWeight={500}
          textAnchor="end"
          opacity={axesOpacity}
        >
          Critical
        </text>

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
      </svg>
    </AbsoluteFill>
  );
};

export default ChartAxes;
