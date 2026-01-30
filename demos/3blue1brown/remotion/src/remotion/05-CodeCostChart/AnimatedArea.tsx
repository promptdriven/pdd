import React from "react";
import { Easing, interpolate, useCurrentFrame, useVideoConfig } from "remotion";
import { CHART_MARGINS, YEAR_RANGE, HOURS_RANGE, DataPoint } from "./constants";

interface AnimatedAreaProps {
  topData: DataPoint[];      // The upper boundary (total cost)
  bottomData: DataPoint[];   // The lower boundary (immediate cost)
  fillColor: string;
  startFrame: number;
  endFrame: number;
}

// Helper to interpolate a value at a given year from a data set
const interpolateAtYear = (data: DataPoint[], year: number): number => {
  if (data.length === 0) return 0;
  if (year <= data[0].year) return data[0].hours;
  if (year >= data[data.length - 1].year) return data[data.length - 1].hours;

  for (let i = 1; i < data.length; i++) {
    if (year <= data[i].year) {
      const t = (year - data[i - 1].year) / (data[i].year - data[i - 1].year);
      return data[i - 1].hours + t * (data[i].hours - data[i - 1].hours);
    }
  }
  return data[data.length - 1].hours;
};

export const AnimatedArea: React.FC<AnimatedAreaProps> = ({
  topData,
  bottomData,
  fillColor,
  startFrame,
  endFrame,
}) => {
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

  // Calculate the draw progress with easing
  const drawProgress = interpolate(frame, [startFrame, endFrame], [0, 1], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.cubic),
  });

  if (drawProgress <= 0) return null;

  // Determine the year range from the actual data (not global YEAR_RANGE)
  // so the area only draws within its data boundaries
  const dataMinYear = Math.min(topData[0].year, bottomData[0].year);
  const dataMaxYear = Math.max(
    topData[topData.length - 1].year,
    bottomData[bottomData.length - 1].year
  );
  const minYear = dataMinYear;
  const maxYear = dataMaxYear;
  const currentMaxYear = minYear + (maxYear - minYear) * drawProgress;

  // Create sample points across the year range for smooth area
  const sampleYears: number[] = [];
  for (let year = minYear; year <= currentMaxYear; year += 2) {
    sampleYears.push(year);
  }
  // Ensure we include the exact current max year
  if (sampleYears[sampleYears.length - 1] !== currentMaxYear) {
    sampleYears.push(currentMaxYear);
  }

  // Build the area path
  // Start from bottom-left, go along bottom line to right, then along top line back to left
  let pathD = "";

  // Bottom line (from left to right)
  sampleYears.forEach((year, i) => {
    const x = getXPosition(year);
    const y = getYPosition(interpolateAtYear(bottomData, year));
    if (i === 0) {
      pathD += `M ${x} ${y}`;
    } else {
      pathD += ` L ${x} ${y}`;
    }
  });

  // Top line (from right to left)
  for (let i = sampleYears.length - 1; i >= 0; i--) {
    const year = sampleYears[i];
    const x = getXPosition(year);
    const y = getYPosition(interpolateAtYear(topData, year));
    pathD += ` L ${x} ${y}`;
  }

  pathD += " Z"; // Close the path

  return (
    <svg
      width={width}
      height={height}
      style={{ position: "absolute", top: 0, left: 0, pointerEvents: "none" }}
    >
      <path
        d={pathD}
        fill={fillColor}
        stroke="none"
      />
    </svg>
  );
};
