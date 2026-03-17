import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  CHART_X,
  CHART_Y,
  CHART_W,
  CHART_H,
  X_MIN,
  X_MAX,
  Y_MAX,
  AXIS_COLOR,
  AXIS_LABEL_COLOR,
  GRID_COLOR,
  FONT_FAMILY,
  MORPH_END,
  MILESTONE_START,
  MILESTONE_END,
  MILESTONES,
  dataToPixelX,
  dataToPixelY,
} from "./constants";

const Y_MAJOR_TICKS = [0, 5, 10, 15, 20];
const X_MAJOR_YEARS = [2015, 2017, 2019, 2021, 2023, 2025];
const X_MINOR_YEARS = [2016, 2018, 2020, 2022, 2024];

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  // Axes fade in during morph phase
  const axesOpacity = interpolate(frame, [0, MORPH_END], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  // Grid fades in slightly after axes
  const gridOpacity = interpolate(frame, [0, MORPH_END], [0, 0.08], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
  });

  // Milestone markers fade in
  const milestoneOpacity = interpolate(
    frame,
    [MILESTONE_START, MILESTONE_END],
    [0, 1],
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
        {/* Horizontal grid lines (dashed) */}
        {Y_MAJOR_TICKS.filter((v) => v > 0).map((val) => {
          const y = dataToPixelY(val);
          return (
            <line
              key={`grid-h-${val}`}
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

        {/* Y-axis line */}
        <line
          x1={CHART_X}
          y1={CHART_Y}
          x2={CHART_X}
          y2={CHART_Y + CHART_H}
          stroke={AXIS_COLOR}
          strokeWidth={1}
          opacity={axesOpacity * 0.25}
        />

        {/* X-axis line */}
        <line
          x1={CHART_X}
          y1={CHART_Y + CHART_H}
          x2={CHART_X + CHART_W}
          y2={CHART_Y + CHART_H}
          stroke={AXIS_COLOR}
          strokeWidth={1}
          opacity={axesOpacity * 0.25}
        />

        {/* X-axis major tick marks and labels */}
        {X_MAJOR_YEARS.map((year) => {
          const x = dataToPixelX(year);
          return (
            <g key={`xtick-major-${year}`}>
              <line
                x1={x}
                y1={CHART_Y + CHART_H}
                x2={x}
                y2={CHART_Y + CHART_H + 8}
                stroke={AXIS_LABEL_COLOR}
                strokeWidth={1}
                opacity={axesOpacity * 0.25}
              />
              <text
                x={x}
                y={CHART_Y + CHART_H + 28}
                fill={AXIS_LABEL_COLOR}
                fontSize={10}
                fontFamily={FONT_FAMILY}
                fontWeight={400}
                textAnchor="middle"
                opacity={axesOpacity * 0.25}
              >
                {year}
              </text>
            </g>
          );
        })}

        {/* X-axis minor tick marks */}
        {X_MINOR_YEARS.map((year) => {
          const x = dataToPixelX(year);
          return (
            <line
              key={`xtick-minor-${year}`}
              x1={x}
              y1={CHART_Y + CHART_H}
              x2={x}
              y2={CHART_Y + CHART_H + 5}
              stroke={AXIS_LABEL_COLOR}
              strokeWidth={1}
              opacity={axesOpacity * 0.15}
            />
          );
        })}

        {/* Y-axis tick marks and labels */}
        {Y_MAJOR_TICKS.map((val) => {
          const y = dataToPixelY(val);
          return (
            <g key={`ytick-${val}`}>
              <line
                x1={CHART_X - 6}
                y1={y}
                x2={CHART_X}
                y2={y}
                stroke={AXIS_LABEL_COLOR}
                strokeWidth={1}
                opacity={axesOpacity * 0.25}
              />
              <text
                x={CHART_X - 14}
                y={y + 4}
                fill={AXIS_LABEL_COLOR}
                fontSize={10}
                fontFamily={FONT_FAMILY}
                fontWeight={400}
                textAnchor="end"
                opacity={axesOpacity * 0.25}
              >
                {val}
              </text>
            </g>
          );
        })}

        {/* X-axis title */}
        <text
          x={CHART_X + CHART_W / 2}
          y={CHART_Y + CHART_H + 56}
          fill={AXIS_LABEL_COLOR}
          fontSize={12}
          fontFamily={FONT_FAMILY}
          fontWeight={400}
          textAnchor="middle"
          opacity={axesOpacity * 0.3}
        >
          Year
        </text>

        {/* Y-axis title (rotated) */}
        <text
          x={CHART_X - 60}
          y={CHART_Y + CHART_H / 2}
          fill={AXIS_LABEL_COLOR}
          fontSize={12}
          fontFamily={FONT_FAMILY}
          fontWeight={400}
          textAnchor="middle"
          transform={`rotate(-90, ${CHART_X - 60}, ${CHART_Y + CHART_H / 2})`}
          opacity={axesOpacity * 0.3}
        >
          Cost (Developer Hours)
        </text>

        {/* AI milestone vertical markers */}
        {MILESTONES.map((ms) => {
          const x = dataToPixelX(ms.year);
          return (
            <g key={`ms-${ms.year}`} opacity={milestoneOpacity * 0.12}>
              {/* Vertical dashed line */}
              <line
                x1={x}
                y1={CHART_Y}
                x2={x}
                y2={CHART_Y + CHART_H}
                stroke={AXIS_LABEL_COLOR}
                strokeWidth={1}
                strokeDasharray="4 3"
              />
              {/* Rotated label at top */}
              <text
                x={x}
                y={CHART_Y - 8}
                fill={AXIS_LABEL_COLOR}
                fontSize={9}
                fontFamily={FONT_FAMILY}
                fontWeight={400}
                textAnchor="end"
                transform={`rotate(-45, ${x}, ${CHART_Y - 8})`}
                opacity={milestoneOpacity * 0.3 / 0.12}
              >
                {ms.label}
              </text>
            </g>
          );
        })}
      </svg>
    </AbsoluteFill>
  );
};

export default ChartAxes;
