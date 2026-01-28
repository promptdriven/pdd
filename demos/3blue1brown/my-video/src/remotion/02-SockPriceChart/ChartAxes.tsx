import React from "react";
import { interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import {
  COLORS,
  CHART_MARGINS,
  YEAR_RANGE,
  HOURS_RANGE,
  BEATS,
} from "./constants";

interface ChartAxesProps {
  opacity?: number;
}

export const ChartAxes: React.FC<ChartAxesProps> = ({ opacity = 1 }) => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const chartWidth = width - CHART_MARGINS.left - CHART_MARGINS.right;
  const chartHeight = height - CHART_MARGINS.top - CHART_MARGINS.bottom;

  // Fade in animation
  const fadeIn = interpolate(
    frame,
    [BEATS.AXES_FADE_IN_START, BEATS.AXES_FADE_IN_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const currentOpacity = fadeIn * opacity;

  const yearTicks = [1950, 1960, 1970, 1980, 1990, 2000, 2010, 2020];
  const hourTicks = [0, 0.5, 1, 1.5, 2, 2.5, 3];

  const getXPosition = (year: number) => {
    return (
      CHART_MARGINS.left +
      ((year - YEAR_RANGE.min) / (YEAR_RANGE.max - YEAR_RANGE.min)) * chartWidth
    );
  };

  const getYPosition = (hours: number) => {
    return (
      CHART_MARGINS.top +
      chartHeight -
      (hours / HOURS_RANGE.max) * chartHeight
    );
  };

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: "100%",
        height: "100%",
        opacity: currentOpacity,
      }}
    >
      {/* Grid lines - horizontal */}
      <svg
        width={width}
        height={height}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {hourTicks.map((hour) => (
          <line
            key={`h-grid-${hour}`}
            x1={CHART_MARGINS.left}
            y1={getYPosition(hour)}
            x2={width - CHART_MARGINS.right}
            y2={getYPosition(hour)}
            stroke={COLORS.GRID}
            strokeWidth={1}
            strokeDasharray="5,5"
            opacity={0.5}
          />
        ))}
        {/* Grid lines - vertical */}
        {yearTicks.map((year) => (
          <line
            key={`v-grid-${year}`}
            x1={getXPosition(year)}
            y1={CHART_MARGINS.top}
            x2={getXPosition(year)}
            y2={height - CHART_MARGINS.bottom}
            stroke={COLORS.GRID}
            strokeWidth={1}
            strokeDasharray="5,5"
            opacity={0.5}
          />
        ))}

        {/* X-axis */}
        <line
          x1={CHART_MARGINS.left}
          y1={height - CHART_MARGINS.bottom}
          x2={width - CHART_MARGINS.right}
          y2={height - CHART_MARGINS.bottom}
          stroke={COLORS.AXIS}
          strokeWidth={2}
        />

        {/* Y-axis */}
        <line
          x1={CHART_MARGINS.left}
          y1={CHART_MARGINS.top}
          x2={CHART_MARGINS.left}
          y2={height - CHART_MARGINS.bottom}
          stroke={COLORS.AXIS}
          strokeWidth={2}
        />
      </svg>

      {/* Year labels */}
      {yearTicks.map((year) => (
        <div
          key={`year-${year}`}
          style={{
            position: "absolute",
            left: getXPosition(year),
            top: height - CHART_MARGINS.bottom + 20,
            transform: "translateX(-50%)",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 28,
            fontWeight: 500,
            color: COLORS.AXIS_LABEL,
          }}
        >
          {year}
        </div>
      ))}

      {/* Hour labels - positioned to the left of the Y-axis */}
      {hourTicks.map((hour) => (
        <div
          key={`hour-${hour}`}
          style={{
            position: "absolute",
            left: CHART_MARGINS.left - 15,
            top: getYPosition(hour),
            transform: "translate(-100%, -50%)",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 28,
            fontWeight: 500,
            color: COLORS.AXIS_LABEL,
            textAlign: "right",
          }}
        >
          {hour}
        </div>
      ))}

      {/* Y-axis label - rotated, positioned far left of numbers */}
      <div
        style={{
          position: "absolute",
          left: 0,
          top: 0,
          width: 70,
          height: "100%",
          display: "flex",
          alignItems: "center",
          justifyContent: "center",
        }}
      >
        <div
          style={{
            transform: "rotate(-90deg)",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 26,
            fontWeight: 600,
            color: COLORS.AXIS_LABEL,
            whiteSpace: "nowrap",
          }}
        >
          Hours of labor to buy / repair
        </div>
      </div>

      {/* X-axis label */}
      <div
        style={{
          position: "absolute",
          left: "50%",
          bottom: 25,
          transform: "translateX(-50%)",
          fontFamily: "Inter, system-ui, sans-serif",
          fontSize: 26,
          fontWeight: 600,
          color: COLORS.AXIS_LABEL,
        }}
      >
        Year
      </div>
    </div>
  );
};
