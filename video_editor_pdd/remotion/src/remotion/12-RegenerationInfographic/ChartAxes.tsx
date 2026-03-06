import React from "react";
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  AXIS_COLOR,
  AXIS_TITLE_COLOR,
  GRID_COLOR,
  MUTED,
  FONT_FAMILY,
} from "./constants";

interface ChartAxesProps {
  opacity: number;
}

const X_TICK_VALUES = [0, 250, 500, 750, 1000];
const Y_TICK_COUNT = 4;

export const ChartAxes: React.FC<ChartAxesProps> = ({ opacity }) => {
  const gridYPositions = Array.from({ length: Y_TICK_COUNT - 1 }, (_, i) => {
    const pct = (i + 1) / Y_TICK_COUNT;
    return CHART_TOP + CHART_HEIGHT * pct;
  });

  return (
    <>
      {/* Grid lines */}
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0, opacity: opacity * 0.15 }}
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
        style={{ position: "absolute", top: 0, left: 0, opacity }}
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
        {/* X-axis tick marks */}
        {X_TICK_VALUES.map((val) => {
          const x = CHART_LEFT + (val / 1000) * CHART_WIDTH;
          return (
            <line
              key={val}
              x1={x}
              y1={CHART_BOTTOM}
              x2={x}
              y2={CHART_BOTTOM + 8}
              stroke={AXIS_COLOR}
              strokeWidth={2}
            />
          );
        })}
      </svg>

      {/* X-axis tick labels */}
      {X_TICK_VALUES.map((val) => {
        const x = CHART_LEFT + (val / 1000) * CHART_WIDTH;
        return (
          <div
            key={val}
            style={{
              position: "absolute",
              left: x - 25,
              top: CHART_BOTTOM + 14,
              width: 50,
              textAlign: "center",
              opacity,
              fontFamily: FONT_FAMILY,
              fontWeight: 400,
              fontSize: 14,
              color: MUTED,
            }}
          >
            {val === 1000 ? "1000+" : val}
          </div>
        );
      })}

      {/* X-axis title */}
      <div
        style={{
          position: "absolute",
          left: CHART_LEFT,
          top: CHART_BOTTOM + 38,
          width: CHART_WIDTH,
          textAlign: "center",
          opacity,
          fontFamily: FONT_FAMILY,
          fontWeight: 500,
          fontSize: 16,
          color: AXIS_TITLE_COLOR,
        }}
      >
        Module Size (lines)
      </div>

      {/* Y-axis title (rotated) */}
      <div
        style={{
          position: "absolute",
          left: CHART_LEFT - 70,
          top: CHART_TOP + CHART_HEIGHT / 2,
          transform: "rotate(-90deg)",
          transformOrigin: "center center",
          opacity,
          fontFamily: FONT_FAMILY,
          fontWeight: 500,
          fontSize: 16,
          color: AXIS_TITLE_COLOR,
          whiteSpace: "nowrap",
        }}
      >
        Defect Rate
      </div>
    </>
  );
};
