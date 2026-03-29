// ChartAxes.tsx — Renders the chart axes, grid lines, axis labels, and title
import React from "react";
import {
  CHART_LEFT,
  CHART_TOP,
  CHART_RIGHT,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  AXIS_COLOR,
  AXIS_LABEL_COLOR,
  GRID_LINE_COLOR,
  FONT_FAMILY,
  AXIS_LABEL_SIZE,
  TITLE_SIZE,
  LABEL_TEXT_COLOR,
  X_AXIS_YEARS,
  Y_AXIS_LABELS,
} from "./constants";

const GRID_ROWS = 4; // 4 horizontal grid lines (at $50, $100, $150, $200)

export const ChartAxes: React.FC = () => {
  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Title */}
      <text
        x={CHART_LEFT + CHART_WIDTH / 2}
        y={CHART_TOP - 50}
        textAnchor="middle"
        fill={LABEL_TEXT_COLOR}
        fontFamily={FONT_FAMILY}
        fontSize={TITLE_SIZE}
        fontWeight={700}
        opacity={0.9}
      >
        Code Cost: Generate vs. Patch
      </text>

      {/* Horizontal grid lines */}
      {Array.from({ length: GRID_ROWS }, (_, i) => {
        const y =
          CHART_BOTTOM - ((i + 1) / GRID_ROWS) * CHART_HEIGHT;
        return (
          <line
            key={`grid-h-${i}`}
            x1={CHART_LEFT}
            y1={y}
            x2={CHART_RIGHT}
            y2={y}
            stroke={GRID_LINE_COLOR}
            strokeWidth={1}
          />
        );
      })}

      {/* Y-axis */}
      <line
        x1={CHART_LEFT}
        y1={CHART_TOP}
        x2={CHART_LEFT}
        y2={CHART_BOTTOM}
        stroke={AXIS_COLOR}
        strokeWidth={2}
      />

      {/* X-axis */}
      <line
        x1={CHART_LEFT}
        y1={CHART_BOTTOM}
        x2={CHART_RIGHT}
        y2={CHART_BOTTOM}
        stroke={AXIS_COLOR}
        strokeWidth={2}
      />

      {/* Y-axis labels */}
      {Y_AXIS_LABELS.map((label, i) => {
        const y =
          CHART_BOTTOM - (i / (Y_AXIS_LABELS.length - 1)) * CHART_HEIGHT;
        return (
          <text
            key={`y-label-${i}`}
            x={CHART_LEFT - 16}
            y={y + 5}
            textAnchor="end"
            fill={AXIS_LABEL_COLOR}
            fontFamily={FONT_FAMILY}
            fontSize={AXIS_LABEL_SIZE}
          >
            {label}
          </text>
        );
      })}

      {/* X-axis labels */}
      {X_AXIS_YEARS.map((year, i) => {
        const x =
          CHART_LEFT + (i / (X_AXIS_YEARS.length - 1)) * CHART_WIDTH;
        return (
          <text
            key={`x-label-${i}`}
            x={x}
            y={CHART_BOTTOM + 36}
            textAnchor="middle"
            fill={AXIS_LABEL_COLOR}
            fontFamily={FONT_FAMILY}
            fontSize={AXIS_LABEL_SIZE}
          >
            {year}
          </text>
        );
      })}

      {/* Y-axis title */}
      <text
        x={CHART_LEFT - 80}
        y={CHART_TOP + CHART_HEIGHT / 2}
        textAnchor="middle"
        fill={AXIS_LABEL_COLOR}
        fontFamily={FONT_FAMILY}
        fontSize={AXIS_LABEL_SIZE}
        transform={`rotate(-90, ${CHART_LEFT - 80}, ${CHART_TOP + CHART_HEIGHT / 2})`}
      >
        Cost per Change ($)
      </text>

      {/* X-axis title */}
      <text
        x={CHART_LEFT + CHART_WIDTH / 2}
        y={CHART_BOTTOM + 70}
        textAnchor="middle"
        fill={AXIS_LABEL_COLOR}
        fontFamily={FONT_FAMILY}
        fontSize={AXIS_LABEL_SIZE}
      >
        Year
      </text>
    </svg>
  );
};
