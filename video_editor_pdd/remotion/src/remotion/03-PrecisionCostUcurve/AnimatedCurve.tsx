import React, { useMemo } from "react";
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  U_CURVE_POINTS,
  CURVE_COLOR,
} from "./constants";

interface AnimatedCurveProps {
  drawProgress: number;
  opacity: number;
}

/**
 * Converts normalized (0-1) data points to chart pixel coordinates
 * and generates a smooth SVG path using Catmull-Rom to cubic Bezier conversion.
 */
function buildSmoothPath(
  points: { x: number; y: number }[]
): string {
  const chartWidth = CHART_RIGHT - CHART_LEFT;
  const chartHeight = CHART_BOTTOM - CHART_TOP;

  // Convert normalized points to pixel coords
  // y is inverted: 0 = bottom (low cost), 1 = top (high cost)
  const px = points.map((p) => ({
    x: CHART_LEFT + p.x * chartWidth,
    y: CHART_BOTTOM - p.y * chartHeight,
  }));

  if (px.length < 2) return "";

  // Start path
  let d = `M ${px[0].x},${px[0].y}`;

  // Use Catmull-Rom to Bezier conversion for smooth curve
  for (let i = 0; i < px.length - 1; i++) {
    const p0 = px[Math.max(0, i - 1)];
    const p1 = px[i];
    const p2 = px[i + 1];
    const p3 = px[Math.min(px.length - 1, i + 2)];

    const tension = 0.3;
    const cp1x = p1.x + (p2.x - p0.x) * tension;
    const cp1y = p1.y + (p2.y - p0.y) * tension;
    const cp2x = p2.x - (p3.x - p1.x) * tension;
    const cp2y = p2.y - (p3.y - p1.y) * tension;

    d += ` C ${cp1x},${cp1y} ${cp2x},${cp2y} ${p2.x},${p2.y}`;
  }

  return d;
}

export const AnimatedCurve: React.FC<AnimatedCurveProps> = ({
  drawProgress,
  opacity,
}) => {
  const pathD = useMemo(() => buildSmoothPath(U_CURVE_POINTS), []);

  // We use a very large strokeDasharray; dashoffset animates from total to 0
  const totalLength = 3000;
  const dashOffset = totalLength * (1 - drawProgress);

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, opacity }}
    >
      <defs>
        <filter id="curveGlow">
          <feGaussianBlur stdDeviation="8" />
        </filter>
      </defs>
      {/* Glow under the curve */}
      <path
        d={pathD}
        fill="none"
        stroke={CURVE_COLOR}
        strokeWidth={12}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={totalLength}
        strokeDashoffset={dashOffset}
        opacity={0.25}
        filter="url(#curveGlow)"
      />
      {/* Main curve */}
      <path
        d={pathD}
        fill="none"
        stroke={CURVE_COLOR}
        strokeWidth={4}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={totalLength}
        strokeDashoffset={dashOffset}
      />
    </svg>
  );
};
