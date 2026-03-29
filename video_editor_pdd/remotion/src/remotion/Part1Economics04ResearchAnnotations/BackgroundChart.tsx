import React from "react";
import {
  CHART_LEFT,
  CHART_TOP,
  CHART_WIDTH,
  CHART_HEIGHT,
  CHART_BOTTOM,
  AXIS_COLOR,
  AXIS_LABEL_COLOR,
  GRID_COLOR,
  AMBER_LINE_COLOR,
  AMBER_DASHED_COLOR,
  FONT_FAMILY,
  SOLID_LINE_POINTS,
  DASHED_LINE_POINTS,
  YEAR_MIN,
  YEAR_MAX,
  COST_MIN,
  COST_MAX,
  Y_AXIS_LABELS,
} from "./constants";

const mapX = (year: number): number =>
  CHART_LEFT + ((year - YEAR_MIN) / (YEAR_MAX - YEAR_MIN)) * CHART_WIDTH;

const mapY = (cost: number): number =>
  CHART_TOP + CHART_HEIGHT - ((cost - COST_MIN) / (COST_MAX - COST_MIN)) * CHART_HEIGHT;

const buildPath = (points: { x: number; y: number }[]): string =>
  points
    .map((p, i) => `${i === 0 ? "M" : "L"} ${mapX(p.x).toFixed(1)} ${mapY(p.y).toFixed(1)}`)
    .join(" ");

const BackgroundChart: React.FC = () => {
  const years = [2020, 2021, 2022, 2023, 2024, 2025, 2026];

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: 1920,
        height: 1080,
      }}
    >
      {/* Chart title */}
      <div
        style={{
          position: "absolute",
          top: 36,
          left: CHART_LEFT,
          fontFamily: FONT_FAMILY,
          fontSize: 22,
          fontWeight: 600,
          color: "#E2E8F0",
          opacity: 0.85,
        }}
      >
        Code Cost: Generate vs. Maintain
      </div>

      {/* Legend */}
      <div
        style={{
          position: "absolute",
          top: 40,
          right: 200,
          display: "flex",
          gap: 28,
          fontFamily: FONT_FAMILY,
          fontSize: 13,
          color: AXIS_LABEL_COLOR,
        }}
      >
        <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
          <div
            style={{
              width: 24,
              height: 3,
              backgroundColor: AMBER_LINE_COLOR,
              borderRadius: 2,
            }}
          />
          <span>Immediate task cost</span>
        </div>
        <div style={{ display: "flex", alignItems: "center", gap: 8 }}>
          <div
            style={{
              width: 24,
              height: 3,
              background: `repeating-linear-gradient(90deg, ${AMBER_DASHED_COLOR} 0px, ${AMBER_DASHED_COLOR} 5px, transparent 5px, transparent 10px)`,
              borderRadius: 2,
            }}
          />
          <span>Total cost (incl. debt)</span>
        </div>
      </div>

      <svg
        width={1920}
        height={1080}
        viewBox="0 0 1920 1080"
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Horizontal grid lines */}
        {Y_AXIS_LABELS.map((_, i) => {
          const y = CHART_TOP + (i / (Y_AXIS_LABELS.length - 1)) * CHART_HEIGHT;
          return (
            <line
              key={`grid-h-${i}`}
              x1={CHART_LEFT}
              y1={y}
              x2={CHART_LEFT + CHART_WIDTH}
              y2={y}
              stroke={GRID_COLOR}
              strokeWidth={1}
            />
          );
        })}

        {/* Vertical grid lines */}
        {years.map((year) => {
          const x = mapX(year);
          return (
            <line
              key={`grid-v-${year}`}
              x1={x}
              y1={CHART_TOP}
              x2={x}
              y2={CHART_BOTTOM}
              stroke={GRID_COLOR}
              strokeWidth={1}
            />
          );
        })}

        {/* Axes */}
        <line
          x1={CHART_LEFT}
          y1={CHART_TOP}
          x2={CHART_LEFT}
          y2={CHART_BOTTOM}
          stroke={AXIS_COLOR}
          strokeWidth={1.5}
        />
        <line
          x1={CHART_LEFT}
          y1={CHART_BOTTOM}
          x2={CHART_LEFT + CHART_WIDTH}
          y2={CHART_BOTTOM}
          stroke={AXIS_COLOR}
          strokeWidth={1.5}
        />

        {/* Y-axis labels */}
        {Y_AXIS_LABELS.map((label, i) => {
          const y =
            CHART_TOP + CHART_HEIGHT - (i / (Y_AXIS_LABELS.length - 1)) * CHART_HEIGHT;
          return (
            <text
              key={`y-label-${i}`}
              x={CHART_LEFT - 14}
              y={y + 4}
              textAnchor="end"
              fill={AXIS_LABEL_COLOR}
              fontFamily={FONT_FAMILY}
              fontSize={12}
            >
              {label}
            </text>
          );
        })}

        {/* X-axis labels */}
        {years.map((year) => (
          <text
            key={`x-label-${year}`}
            x={mapX(year)}
            y={CHART_BOTTOM + 24}
            textAnchor="middle"
            fill={AXIS_LABEL_COLOR}
            fontFamily={FONT_FAMILY}
            fontSize={12}
          >
            {year}
          </text>
        ))}

        {/* Solid amber line — immediate task cost (dropping) */}
        <path
          d={buildPath(SOLID_LINE_POINTS)}
          fill="none"
          stroke={AMBER_LINE_COLOR}
          strokeWidth={2.5}
          strokeLinecap="round"
          strokeLinejoin="round"
        />

        {/* Dashed amber line — total cost with debt (flat/rising) */}
        <path
          d={buildPath(DASHED_LINE_POINTS)}
          fill="none"
          stroke={AMBER_DASHED_COLOR}
          strokeWidth={2.5}
          strokeDasharray="8 6"
          strokeLinecap="round"
          strokeLinejoin="round"
          opacity={0.7}
        />
      </svg>
    </div>
  );
};

export default BackgroundChart;
