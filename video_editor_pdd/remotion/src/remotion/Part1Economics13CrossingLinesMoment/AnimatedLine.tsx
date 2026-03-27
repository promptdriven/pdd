import React from "react";
import {
  CHART_LEFT,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN_YEAR,
  X_MAX_YEAR,
  Y_MAX,
} from "./constants";

function yearToX(year: number): number {
  return CHART_LEFT + ((year - X_MIN_YEAR) / (X_MAX_YEAR - X_MIN_YEAR)) * CHART_WIDTH;
}

function costToY(cost: number): number {
  return CHART_BOTTOM - (cost / Y_MAX) * CHART_HEIGHT;
}

export interface AnimatedLineProps {
  /** Array of [year, cost] data points */
  points: [number, number][];
  color: string;
  strokeWidth: number;
  /** How many points are revealed (float; fractional means partial segment) */
  revealCount: number;
  dashArray?: string;
  opacity?: number;
}

/**
 * Renders an SVG polyline that progressively reveals based on revealCount.
 * revealCount = points.length means fully drawn.
 */
export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  points,
  color,
  strokeWidth,
  revealCount,
  dashArray,
  opacity = 1,
}) => {
  if (points.length < 2) return null;

  // Clamp revealCount
  const clamped = Math.max(1, Math.min(revealCount, points.length));
  const wholePoints = Math.floor(clamped);
  const frac = clamped - wholePoints;

  // Build revealed path
  const revealedSegments: string[] = [];
  for (let i = 0; i < wholePoints && i < points.length; i++) {
    const [year, cost] = points[i];
    const x = yearToX(year);
    const y = costToY(cost);
    revealedSegments.push(`${i === 0 ? "M" : "L"} ${x} ${y}`);
  }

  // Add fractional segment
  if (frac > 0 && wholePoints < points.length) {
    const [prevYear, prevCost] = points[wholePoints - 1];
    const [nextYear, nextCost] = points[wholePoints];
    const interpYear = prevYear + (nextYear - prevYear) * frac;
    const interpCost = prevCost + (nextCost - prevCost) * frac;
    const x = yearToX(interpYear);
    const y = costToY(interpCost);
    revealedSegments.push(`L ${x} ${y}`);
  }

  const pathD = revealedSegments.join(" ");

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={dashArray}
        opacity={opacity}
      />
    </svg>
  );
};

export default AnimatedLine;
