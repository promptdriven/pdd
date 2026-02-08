import React from "react";
import { Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import {
  BEATS,
  COLORS,
  CHART_MARGINS,
  YEAR_RANGE,
  HOURS_RANGE,
  CROSSING_POINT,
  CHART_DATA,
  YEAR_COUNTER,
} from "./constants";

export const ShadedRegion: React.FC = () => {
  const frame = useCurrentFrame();
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

  // Calculate current animated year
  const currentYear = interpolate(
    frame,
    [BEATS.TIME_PROGRESS_START, BEATS.TIME_PROGRESS_END],
    [YEAR_COUNTER.startYear, YEAR_COUNTER.endYear],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Region fade in
  const regionOpacity = interpolate(
    frame,
    [BEATS.SHADED_REGION_FADE_START, BEATS.SHADED_REGION_FADE_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.cubic),
    }
  );

  // Only show if past the crossing point
  if (currentYear <= CROSSING_POINT.year || regionOpacity <= 0) {
    return null;
  }

  // Get the cost to buy value at current year by interpolating
  const getCostToBuyAtYear = (year: number): number => {
    const data = CHART_DATA.costToBuyFull;
    for (let i = 0; i < data.length - 1; i++) {
      if (year >= data[i].year && year <= data[i + 1].year) {
        const t = (year - data[i].year) / (data[i + 1].year - data[i].year);
        return data[i].hours + t * (data[i + 1].hours - data[i].hours);
      }
    }
    return data[data.length - 1].hours;
  };

  // Build the shaded region path
  // From crossing point, along the buy line, down to x-axis, back to crossing point
  const crossingX = getXPosition(CROSSING_POINT.year);
  const crossingY = getYPosition(CROSSING_POINT.hours);
  const repairY = getYPosition(0.5); // Repair line Y position

  // Limit to current animated year
  const rightBoundYear = Math.min(currentYear, YEAR_RANGE.max);
  const rightBoundX = getXPosition(rightBoundYear);
  const buyValueAtRightBound = getCostToBuyAtYear(rightBoundYear);
  const rightBoundBuyY = getYPosition(buyValueAtRightBound);

  // Build path for the shaded region between repair line and buy line
  // Start at crossing point, go along buy line to current year, up to repair line, back to crossing
  let pathD = `M ${crossingX} ${crossingY}`;

  // Add points along the buy line from crossing point to current year
  for (const point of CHART_DATA.costToBuyFull) {
    if (point.year > CROSSING_POINT.year && point.year <= rightBoundYear) {
      pathD += ` L ${getXPosition(point.year)} ${getYPosition(point.hours)}`;
    }
  }

  // If current year is between data points, add the interpolated point
  if (rightBoundYear > CROSSING_POINT.year) {
    pathD += ` L ${rightBoundX} ${rightBoundBuyY}`;
  }

  // Go up to repair line
  pathD += ` L ${rightBoundX} ${repairY}`;

  // Go back along repair line to crossing point
  pathD += ` L ${crossingX} ${crossingY}`;

  // Close the path
  pathD += " Z";

  // Label fade in (after region is mostly visible)
  const labelOpacity = interpolate(
    frame,
    [BEATS.SHADED_REGION_FADE_END, BEATS.SHADED_REGION_FADE_END + 30],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Calculate label position (center of region)
  const labelX = getXPosition((CROSSING_POINT.year + rightBoundYear) / 2);
  const labelY = (repairY + getYPosition(getCostToBuyAtYear((CROSSING_POINT.year + rightBoundYear) / 2))) / 2;

  return (
    <>
      <svg
        width={width}
        height={height}
        style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
      >
        <defs>
          {/* Gradient for shaded region */}
          <linearGradient id="irrationalGradient" x1="0%" y1="0%" x2="0%" y2="100%">
            <stop offset="0%" stopColor={COLORS.LINE_REPAIR} stopOpacity="0.3" />
            <stop offset="100%" stopColor={COLORS.LINE_REPAIR} stopOpacity="0.1" />
          </linearGradient>

          {/* Pattern for visual interest */}
          <pattern id="stripePattern" patternUnits="userSpaceOnUse" width="8" height="8" patternTransform="rotate(45)">
            <line x1="0" y1="0" x2="0" y2="8" stroke={COLORS.LINE_REPAIR} strokeWidth="2" strokeOpacity="0.15" />
          </pattern>
        </defs>

        {/* Shaded region */}
        <path
          d={pathD}
          fill="url(#irrationalGradient)"
          opacity={regionOpacity}
        />

        {/* Stripe overlay for texture */}
        <path
          d={pathD}
          fill="url(#stripePattern)"
          opacity={regionOpacity * 0.5}
        />

        {/* Border of the region */}
        <path
          d={pathD}
          fill="none"
          stroke={COLORS.LINE_REPAIR}
          strokeWidth={2}
          strokeDasharray="8,4"
          opacity={regionOpacity * 0.6}
        />
      </svg>

      {/* Label for the region */}
      {labelOpacity > 0 && rightBoundYear > CROSSING_POINT.year + 5 && (
        <div
          style={{
            position: "absolute",
            left: labelX,
            top: labelY,
            transform: "translate(-50%, -50%)",
            opacity: labelOpacity * regionOpacity,
            fontFamily: "Inter, system-ui, sans-serif",
            fontSize: 18,
            fontWeight: 400,
            fontStyle: "italic",
            color: COLORS.LINE_REPAIR,
            textShadow: "0 2px 10px rgba(0,0,0,0.8)",
            whiteSpace: "nowrap",
            padding: "8px 16px",
            backgroundColor: "rgba(26, 26, 46, 0.85)",
            borderRadius: 6,
            border: `1px solid ${COLORS.LINE_REPAIR}`,
          }}
        >
          Darning is irrational
        </div>
      )}
    </>
  );
};
