import React from "react";
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  AXIS_COLOR,
  AXIS_TITLE_COLOR,
  GRID_COLOR,
  RED,
  AMBER,
  FONT_FAMILY,
} from "./constants";

interface ChartAxesProps {
  axisOpacity: number;
  gridOpacity: number;
}

export const ChartAxes: React.FC<ChartAxesProps> = ({
  axisOpacity,
  gridOpacity,
}) => {
  const gridYPositions = [0.25, 0.5, 0.75].map(
    (pct) => CHART_TOP + (CHART_BOTTOM - CHART_TOP) * pct
  );

  return (
    <>
      {/* Grid lines */}
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0, opacity: gridOpacity }}
      >
        {gridYPositions.map((y, i) => (
          <line
            key={i}
            x1={CHART_LEFT}
            y1={y}
            x2={CHART_RIGHT}
            y2={y}
            stroke={GRID_COLOR}
            strokeWidth={1}
            strokeDasharray="8 6"
          />
        ))}
      </svg>

      {/* Axis lines */}
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0, opacity: axisOpacity }}
      >
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
        {/* Tick marks on X axis */}
        {[0, 0.25, 0.5, 0.75, 1].map((pct, i) => {
          const x = CHART_LEFT + (CHART_RIGHT - CHART_LEFT) * pct;
          return (
            <line
              key={i}
              x1={x}
              y1={CHART_BOTTOM}
              x2={x}
              y2={CHART_BOTTOM + 8}
              stroke={AXIS_COLOR}
              strokeWidth={2}
            />
          );
        })}
        {/* Tick marks on Y axis */}
        {[0, 0.25, 0.5, 0.75, 1].map((pct, i) => {
          const y = CHART_TOP + (CHART_BOTTOM - CHART_TOP) * pct;
          return (
            <line
              key={i}
              x1={CHART_LEFT - 8}
              y1={y}
              x2={CHART_LEFT}
              y2={y}
              stroke={AXIS_COLOR}
              strokeWidth={2}
            />
          );
        })}
      </svg>

      {/* X-axis title — centered below the X-axis */}
      <div
        style={{
          position: "absolute",
          left: CHART_LEFT,
          top: CHART_BOTTOM + 50,
          width: CHART_RIGHT - CHART_LEFT,
          textAlign: "center",
          opacity: axisOpacity,
          fontFamily: FONT_FAMILY,
          fontWeight: 500,
          fontSize: 20,
          color: AXIS_TITLE_COLOR,
        }}
      >
        Prompt Precision
      </div>

      {/* Y-axis title (rotated) */}
      <div
        style={{
          position: "absolute",
          left: CHART_LEFT - 80,
          top: (CHART_TOP + CHART_BOTTOM) / 2,
          transform: "rotate(-90deg)",
          transformOrigin: "center center",
          opacity: axisOpacity,
          fontFamily: FONT_FAMILY,
          fontWeight: 500,
          fontSize: 20,
          color: AXIS_TITLE_COLOR,
          whiteSpace: "nowrap",
        }}
      >
        Effective Cost
      </div>

      {/* X-axis endpoint labels */}
      <div
        style={{
          position: "absolute",
          left: CHART_LEFT - 10,
          top: CHART_BOTTOM + 14,
          opacity: axisOpacity,
          fontFamily: FONT_FAMILY,
          fontWeight: 600,
          fontSize: 16,
          color: RED,
        }}
      >
        Vague
      </div>
      <div
        style={{
          position: "absolute",
          right: 1920 - CHART_RIGHT - 10,
          top: CHART_BOTTOM + 14,
          opacity: axisOpacity,
          fontFamily: FONT_FAMILY,
          fontWeight: 600,
          fontSize: 16,
          color: AMBER,
          textAlign: "right",
        }}
      >
        Over-Specified
      </div>

      {/* Y-axis endpoint labels */}
      <div
        style={{
          position: "absolute",
          left: CHART_LEFT - 50,
          top: CHART_BOTTOM - 10,
          opacity: axisOpacity,
          fontFamily: FONT_FAMILY,
          fontWeight: 500,
          fontSize: 18,
          color: AXIS_COLOR,
        }}
      >
        Low
      </div>
      <div
        style={{
          position: "absolute",
          left: CHART_LEFT - 52,
          top: CHART_TOP - 5,
          opacity: axisOpacity,
          fontFamily: FONT_FAMILY,
          fontWeight: 500,
          fontSize: 18,
          color: AXIS_COLOR,
        }}
      >
        High
      </div>
    </>
  );
};
