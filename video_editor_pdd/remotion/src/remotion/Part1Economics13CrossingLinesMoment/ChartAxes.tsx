import React from "react";
import { AbsoluteFill } from "remotion";
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  AXIS_COLOR,
  AXIS_LABEL_COLOR,
  GRID_LINE_COLOR,
  FONT_FAMILY,
  AXIS_FONT_SIZE,
  X_MIN_YEAR,
  X_MAX_YEAR,
} from "./constants";

const YEAR_TICKS = [2020, 2021, 2022, 2023, 2024, 2025, 2026];

const COST_TICKS = [
  { value: 0, label: "$0" },
  { value: 20, label: "" },
  { value: 40, label: "" },
  { value: 60, label: "" },
  { value: 80, label: "" },
  { value: 100, label: "High" },
];

function yearToX(year: number): number {
  return CHART_LEFT + ((year - X_MIN_YEAR) / (X_MAX_YEAR - X_MIN_YEAR)) * CHART_WIDTH;
}

function costToY(cost: number): number {
  return CHART_BOTTOM - (cost / 100) * CHART_HEIGHT;
}

export const ChartAxes: React.FC = () => {
  return (
    <AbsoluteFill>
      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Grid lines (horizontal) */}
        {COST_TICKS.map((tick) => (
          <line
            key={`grid-h-${tick.value}`}
            x1={CHART_LEFT}
            y1={costToY(tick.value)}
            x2={CHART_RIGHT}
            y2={costToY(tick.value)}
            stroke={GRID_LINE_COLOR}
            strokeWidth={1}
          />
        ))}

        {/* Grid lines (vertical) */}
        {YEAR_TICKS.map((year) => (
          <line
            key={`grid-v-${year}`}
            x1={yearToX(year)}
            y1={CHART_TOP}
            x2={yearToX(year)}
            y2={CHART_BOTTOM}
            stroke={GRID_LINE_COLOR}
            strokeWidth={1}
          />
        ))}

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

        {/* X axis labels */}
        {YEAR_TICKS.map((year) => (
          <text
            key={`xlabel-${year}`}
            x={yearToX(year)}
            y={CHART_BOTTOM + 30}
            textAnchor="middle"
            fill={AXIS_LABEL_COLOR}
            fontFamily={FONT_FAMILY}
            fontSize={AXIS_FONT_SIZE}
          >
            {year}
          </text>
        ))}

        {/* Y axis labels */}
        <text
          x={CHART_LEFT - 20}
          y={costToY(100)}
          textAnchor="end"
          dominantBaseline="middle"
          fill={AXIS_LABEL_COLOR}
          fontFamily={FONT_FAMILY}
          fontSize={AXIS_FONT_SIZE}
        >
          High
        </text>
        <text
          x={CHART_LEFT - 20}
          y={costToY(0)}
          textAnchor="end"
          dominantBaseline="middle"
          fill={AXIS_LABEL_COLOR}
          fontFamily={FONT_FAMILY}
          fontSize={AXIS_FONT_SIZE}
        >
          Low
        </text>

        {/* Chart title */}
        <text
          x={CHART_LEFT + CHART_WIDTH / 2}
          y={CHART_TOP - 40}
          textAnchor="middle"
          fill="#E2E8F0"
          fontFamily={FONT_FAMILY}
          fontSize={20}
          fontWeight={600}
        >
          Cost to Fix vs. Cost to Generate
        </text>

        {/* Y-axis title */}
        <text
          x={CHART_LEFT - 70}
          y={CHART_TOP + CHART_HEIGHT / 2}
          textAnchor="middle"
          fill={AXIS_LABEL_COLOR}
          fontFamily={FONT_FAMILY}
          fontSize={AXIS_FONT_SIZE}
          transform={`rotate(-90, ${CHART_LEFT - 70}, ${CHART_TOP + CHART_HEIGHT / 2})`}
        >
          Relative Cost
        </text>
      </svg>
    </AbsoluteFill>
  );
};

export default ChartAxes;
