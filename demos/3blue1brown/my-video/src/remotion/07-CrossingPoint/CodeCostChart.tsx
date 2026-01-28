import React from "react";
import { interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import {
  COLORS,
  CHART_DATA,
  CHART_MARGINS,
  YEAR_RANGE,
  HOURS_RANGE,
  BEATS,
} from "./constants";

export const CodeCostChart: React.FC = () => {
  const frame = useCurrentFrame();
  const { width, height } = useVideoConfig();

  const chartWidth = width - CHART_MARGINS.left - CHART_MARGINS.right;
  const chartHeight = height - CHART_MARGINS.top - CHART_MARGINS.bottom;

  // Zoom out effect: start zoomed in on right side, zoom out to full view
  const zoomScale = interpolate(
    frame,
    [BEATS.ZOOM_OUT_START, BEATS.ZOOM_OUT_END],
    [1.5, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const zoomOffsetX = interpolate(
    frame,
    [BEATS.ZOOM_OUT_START, BEATS.ZOOM_OUT_END],
    [-300, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const zoomOffsetY = interpolate(
    frame,
    [BEATS.ZOOM_OUT_START, BEATS.ZOOM_OUT_END],
    [-100, 0],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

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

  // Build path for Cost to Generate line
  const generateLinePoints = CHART_DATA.costToGenerate
    .map((d, i) => {
      const x = getXPosition(d.year);
      const y = getYPosition(d.hours);
      return `${i === 0 ? "M" : "L"} ${x} ${y}`;
    })
    .join(" ");

  // Build path for Cost to Patch line (straight horizontal)
  const patchStart = CHART_DATA.costToPatch[0];
  const patchEnd = CHART_DATA.costToPatch[1];
  const patchLinePath = `M ${getXPosition(patchStart.year)} ${getYPosition(patchStart.hours)} L ${getXPosition(patchEnd.year)} ${getYPosition(patchEnd.hours)}`;

  const yearTicks = [2015, 2018, 2020, 2022, 2024, 2026, 2028, 2030];
  const hourTicks = [0, 0.5, 1, 1.5, 2, 2.5, 3];

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: "100%",
        height: "100%",
        transform: `scale(${zoomScale}) translate(${zoomOffsetX}px, ${zoomOffsetY}px)`,
        transformOrigin: "center center",
      }}
    >
      {/* Grid and axes */}
      <svg
        width={width}
        height={height}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {/* Horizontal grid lines */}
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

        {/* Vertical grid lines */}
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

        {/* Cost to Generate line (blue) */}
        <path
          d={generateLinePoints}
          fill="none"
          stroke={COLORS.LINE_GENERATE}
          strokeWidth={4}
          strokeLinecap="round"
          strokeLinejoin="round"
        />

        {/* Cost to Patch line (amber) */}
        <path
          d={patchLinePath}
          fill="none"
          stroke={COLORS.LINE_PATCH}
          strokeWidth={4}
          strokeLinecap="round"
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
            fontSize: 24,
            fontWeight: 500,
            color: COLORS.AXIS_LABEL,
          }}
        >
          {year}
        </div>
      ))}

      {/* Hour labels */}
      {hourTicks.map((hour) => (
        <div
          key={`hour-${hour}`}
          style={{
            position: "absolute",
            left: CHART_MARGINS.left - 15,
            top: getYPosition(hour),
            transform: "translate(-100%, -50%)",
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 24,
            fontWeight: 500,
            color: COLORS.AXIS_LABEL,
            textAlign: "right",
          }}
        >
          {hour}h
        </div>
      ))}

      {/* Y-axis label */}
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
            fontSize: 22,
            fontWeight: 600,
            color: COLORS.AXIS_LABEL,
            whiteSpace: "nowrap",
          }}
        >
          Developer hours per feature
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
          fontSize: 22,
          fontWeight: 600,
          color: COLORS.AXIS_LABEL,
        }}
      >
        Year
      </div>
    </div>
  );
};
