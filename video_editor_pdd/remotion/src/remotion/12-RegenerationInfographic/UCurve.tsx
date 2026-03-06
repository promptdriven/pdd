import React, { useMemo } from "react";
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  CHART_WIDTH,
  CHART_HEIGHT,
  U_CURVE_POINTS,
  AMBER,
  RED,
} from "./constants";

interface UCurveProps {
  drawProgress: number;
  opacity: number;
}

/**
 * Converts normalized (0-1) data points to chart pixel coordinates
 * and generates a smooth SVG path using Catmull-Rom to cubic Bezier conversion.
 */
function buildSmoothPath(points: { x: number; y: number }[]): string {
  // Convert normalized points to pixel coords
  // y is inverted: 0 = bottom (low defect), 1 = top (high defect)
  const px = points.map((p) => ({
    x: CHART_LEFT + p.x * CHART_WIDTH,
    y: CHART_BOTTOM - p.y * CHART_HEIGHT,
  }));

  if (px.length < 2) return "";

  let d = `M ${px[0].x},${px[0].y}`;

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

/**
 * Build a closed fill path from the curve down to the chart bottom.
 */
function buildFillPath(points: { x: number; y: number }[]): string {
  const px = points.map((p) => ({
    x: CHART_LEFT + p.x * CHART_WIDTH,
    y: CHART_BOTTOM - p.y * CHART_HEIGHT,
  }));

  if (px.length < 2) return "";

  let d = `M ${px[0].x},${CHART_BOTTOM}`;
  d += ` L ${px[0].x},${px[0].y}`;

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

  d += ` L ${px[px.length - 1].x},${CHART_BOTTOM} Z`;
  return d;
}

export const UCurve: React.FC<UCurveProps> = ({ drawProgress, opacity }) => {
  const pathD = useMemo(() => buildSmoothPath(U_CURVE_POINTS), []);
  const fillD = useMemo(() => buildFillPath(U_CURVE_POINTS), []);

  const totalLength = 3000;
  const dashOffset = totalLength * (1 - drawProgress);

  // Danger zone tint regions
  const leftDangerEnd = CHART_LEFT + 0.1 * CHART_WIDTH;
  const rightDangerStart = CHART_LEFT + 0.7 * CHART_WIDTH;

  return (
    <svg
      width={1920}
      height={1080}
      viewBox="0 0 1920 1080"
      style={{ position: "absolute", top: 0, left: 0, opacity }}
    >
      <defs>
        <linearGradient id="curveGradFill" x1="0" y1="0" x2="0" y2="1">
          <stop offset="0%" stopColor={AMBER} stopOpacity={0.1} />
          <stop offset="100%" stopColor={AMBER} stopOpacity={0.02} />
        </linearGradient>
        <filter id="ucurveGlow">
          <feGaussianBlur stdDeviation="8" />
        </filter>
        <clipPath id="drawClip">
          <rect
            x={CHART_LEFT}
            y={CHART_TOP}
            width={CHART_WIDTH * drawProgress}
            height={CHART_HEIGHT}
          />
        </clipPath>
      </defs>

      {/* Faint danger zone tints */}
      <rect
        x={CHART_LEFT}
        y={CHART_TOP}
        width={leftDangerEnd - CHART_LEFT}
        height={CHART_HEIGHT}
        fill={RED}
        opacity={0.06 * drawProgress}
      />
      <rect
        x={rightDangerStart}
        y={CHART_TOP}
        width={CHART_RIGHT - rightDangerStart}
        height={CHART_HEIGHT}
        fill={RED}
        opacity={0.06 * drawProgress}
      />

      {/* Fill under curve — clipped to draw progress */}
      <path
        d={fillD}
        fill="url(#curveGradFill)"
        clipPath="url(#drawClip)"
      />

      {/* Glow under curve */}
      <path
        d={pathD}
        fill="none"
        stroke={AMBER}
        strokeWidth={12}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={totalLength}
        strokeDashoffset={dashOffset}
        opacity={0.25}
        filter="url(#ucurveGlow)"
      />

      {/* Main curve */}
      <path
        d={pathD}
        fill="none"
        stroke={AMBER}
        strokeWidth={3}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={totalLength}
        strokeDashoffset={dashOffset}
      />
    </svg>
  );
};
