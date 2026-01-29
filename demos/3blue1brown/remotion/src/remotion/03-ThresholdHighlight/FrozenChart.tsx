import React from "react";
import { useVideoConfig } from "remotion";
import {
  COLORS,
  CHART_DATA,
  CHART_MARGINS,
  YEAR_RANGE,
  HOURS_RANGE,
} from "./constants";

export const FrozenChart: React.FC = () => {
  const { width, height } = useVideoConfig();

  const chartWidth = width - CHART_MARGINS.left - CHART_MARGINS.right;
  const chartHeight = height - CHART_MARGINS.top - CHART_MARGINS.bottom;

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

  // Build path for Cost to Buy line
  const buyLinePoints = CHART_DATA.costToBuy
    .map((d, i) => {
      const x = getXPosition(d.year);
      const y = getYPosition(d.hours);
      return `${i === 0 ? "M" : "L"} ${x} ${y}`;
    })
    .join(" ");

  // Build path for Cost to Repair line (straight horizontal)
  const repairStart = CHART_DATA.costToRepair[0];
  const repairEnd = CHART_DATA.costToRepair[1];
  const repairLinePath = `M ${getXPosition(repairStart.year)} ${getYPosition(repairStart.hours)} L ${getXPosition(repairEnd.year)} ${getYPosition(repairEnd.hours)}`;

  const yearTicks = [1950, 1960, 1970, 1980, 1990, 2000, 2010, 2020];
  const hourTicks = [0, 0.5, 1, 1.5];

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: "100%",
        height: "100%",
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

        {/* Cost to Buy line (frozen/complete) */}
        <path
          d={buyLinePoints}
          fill="none"
          stroke={COLORS.LINE_BUY}
          strokeWidth={4}
          strokeLinecap="round"
          strokeLinejoin="round"
        />

        {/* Cost to Repair line (frozen/complete) */}
        <path
          d={repairLinePath}
          fill="none"
          stroke={COLORS.LINE_REPAIR}
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
            fontSize: 28,
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
            fontSize: 28,
            fontWeight: 500,
            color: COLORS.AXIS_LABEL,
            textAlign: "right",
          }}
        >
          {hour}
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
            fontSize: 26,
            fontWeight: 600,
            color: COLORS.AXIS_LABEL,
            whiteSpace: "nowrap",
          }}
        >
          Hours of labor to buy / repair a sock
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
