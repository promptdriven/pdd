import React from "react";
import { interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import {
  COLORS,
  CHART_DATA,
  CHART_MARGINS,
  YEAR_RANGE,
  HOURS_RANGE,
  BEATS,
  interpolateHours,
  DataPoint,
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

  // Build SVG path from data points
  const buildPath = (data: DataPoint[]) => {
    return data
      .map((d, i) => {
        const x = getXPosition(d.year);
        const y = getYPosition(d.hours);
        return `${i === 0 ? "M" : "L"} ${x} ${y}`;
      })
      .join(" ");
  };

  // Build tech debt shaded area between large CB immediate and total cost (2020-2025)
  const buildTechDebtArea = () => {
    const startYear = 2020;
    const endYear = 2025;
    const steps = 20;

    // Top edge (total cost) left to right
    let path = `M ${getXPosition(startYear)} ${getYPosition(interpolateHours(CHART_DATA.totalCostLargeCodebase, startYear))}`;
    for (let i = 1; i <= steps; i++) {
      const year = startYear + (endYear - startYear) * (i / steps);
      path += ` L ${getXPosition(year)} ${getYPosition(interpolateHours(CHART_DATA.totalCostLargeCodebase, year))}`;
    }
    // Bottom edge (large CB immediate) right to left
    for (let i = steps; i >= 0; i--) {
      const year = startYear + (endYear - startYear) * (i / steps);
      path += ` L ${getXPosition(year)} ${getYPosition(interpolateHours(CHART_DATA.immediateCostLargeCodebase, year))}`;
    }
    path += " Z";
    return path;
  };

  const yearTicks = [2016, 2018, 2020, 2022, 2024];
  const yearLabels = [2015, 2020, 2025];
  const hourTicks = [0, 5, 10, 15, 20, 25, 30, 35];

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

        {/* Tech debt shaded area (between large CB immediate and total cost) */}
        <path
          d={buildTechDebtArea()}
          fill={COLORS.AREA_TECH_DEBT}
        />

        {/* Cost to Generate line (blue, solid) */}
        <path
          d={buildPath(CHART_DATA.costToGenerate)}
          fill="none"
          stroke={COLORS.LINE_GENERATE}
          strokeWidth={4}
          strokeLinecap="round"
          strokeLinejoin="round"
        />

        {/* Immediate cost baseline (amber, solid, pre-fork 2015-2020) */}
        <path
          d={buildPath(CHART_DATA.immediateCostBaseline)}
          fill="none"
          stroke={COLORS.LINE_PATCH}
          strokeWidth={3}
          strokeLinecap="round"
        />

        {/* Small codebase fork (amber, lower opacity as contrast) */}
        <path
          d={buildPath(CHART_DATA.immediateCostSmallCodebase)}
          fill="none"
          stroke={COLORS.LINE_PATCH}
          strokeWidth={3}
          strokeLinecap="round"
          opacity={0.35}
        />

        {/* Large codebase fork (amber, solid) */}
        <path
          d={buildPath(CHART_DATA.immediateCostLargeCodebase)}
          fill="none"
          stroke={COLORS.LINE_PATCH}
          strokeWidth={3}
          strokeLinecap="round"
          opacity={0.7}
        />

        {/* Total cost large codebase (amber, dashed) */}
        <path
          d={buildPath(CHART_DATA.totalCostLargeCodebase)}
          fill="none"
          stroke={COLORS.LINE_PATCH_TOTAL}
          strokeWidth={3}
          strokeLinecap="round"
          strokeDasharray="12,6"
          opacity={0.9}
        />
      </svg>

      {/* Year labels */}
      {yearLabels.map((year) => (
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
      {hourTicks
        .filter((h) => h % 10 === 0 || h === 5 || h === 15 || h === 25 || h === 35)
        .map((hour) => (
          <div
            key={`hour-${hour}`}
            style={{
              position: "absolute",
              left: CHART_MARGINS.left - 15,
              top: getYPosition(hour),
              transform: "translate(-100%, -50%)",
              fontFamily: "Inter, system-ui, sans-serif",
              fontSize: 22,
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
          Developer hours per module
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
