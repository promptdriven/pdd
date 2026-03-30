import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  type DataPoint,
  X_MIN,
  X_MAX,
  xToPixel,
  yToPixel,
  interpolateY,
  LINES_START,
  LINES_END,
} from "./constants";

interface AnimatedLineProps {
  data: DataPoint[];
  color: string;
  strokeWidth: number;
  label: string;
  labelX?: number;  // x position for legend label (pixel)
  labelY?: number;  // y position for legend label (pixel)
}

/**
 * Draws a data line progressively from left to right.
 * Uses cubic easing with a slight slowdown near the crossing point.
 */
export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  data,
  color,
  strokeWidth,
  label,
  labelX,
  labelY,
}) => {
  const frame = useCurrentFrame();

  // Calculate the current "reveal year" based on animation progress.
  // The line draws from 1950 to 2020 over LINES_START → LINES_END frames.
  // We slow down near the crossing point for dramatic effect.
  const rawProgress = interpolate(
    frame,
    [LINES_START, LINES_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp", easing: Easing.inOut(Easing.cubic) }
  );

  // Map progress to year with a slight deceleration zone around crossing
  const currentYear = X_MIN + rawProgress * (X_MAX - X_MIN);

  // Don't draw anything before lines start
  if (frame < LINES_START) return null;

  // Build SVG path up to currentYear
  const samplesPerYear = 2;
  const totalSamples = Math.ceil((currentYear - X_MIN) * samplesPerYear);
  if (totalSamples <= 0) return null;

  let pathD = "";
  for (let i = 0; i <= totalSamples; i++) {
    const year = X_MIN + (i / samplesPerYear);
    if (year > currentYear) break;
    const px = xToPixel(year);
    const py = yToPixel(interpolateY(data, year));
    if (i === 0) {
      pathD += `M ${px} ${py}`;
    } else {
      pathD += ` L ${px} ${py}`;
    }
  }

  // Final point at exactly currentYear
  const finalPx = xToPixel(currentYear);
  const finalPy = yToPixel(interpolateY(data, currentYear));
  pathD += ` L ${finalPx} ${finalPy}`;

  // Label opacity: fade in once the line has drawn past 1955
  const labelOpacity = interpolate(
    currentYear,
    [1954, 1958],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Legend label position (near end of line, or custom)
  const legendX = labelX ?? finalPx + 12;
  const legendY = labelY ?? finalPy;

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      {/* Glow behind line */}
      <defs>
        <filter id={`glow-${label.replace(/\s/g, "")}`}>
          <feGaussianBlur stdDeviation="3" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
        strokeLinejoin="round"
        filter={`url(#glow-${label.replace(/\s/g, "")})`}
      />

      {/* Dot at the tip of the line */}
      <circle
        cx={finalPx}
        cy={finalPy}
        r={4}
        fill={color}
        opacity={0.9}
      />

      {/* Series label near the line start area */}
      {labelOpacity > 0 && (
        <text
          x={xToPixel(X_MIN) + 8}
          y={yToPixel(interpolateY(data, X_MIN)) - 12}
          fill={color}
          fontSize={14}
          fontFamily="Inter, sans-serif"
          fontWeight={600}
          opacity={labelOpacity * 0.85}
        >
          {label}
        </text>
      )}
    </svg>
  );
};

export default AnimatedLine;
