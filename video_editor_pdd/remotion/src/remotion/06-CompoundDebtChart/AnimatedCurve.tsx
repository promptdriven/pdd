import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";

const WIDTH = 1920;
const HEIGHT = 1080;
const CHART_X = 200;
const CHART_Y = 80;
const CHART_W = 1620;
const CHART_H = 800;
const FONT_FAMILY = "Inter, sans-serif";

interface Point {
  x: number;
  y: number;
}

interface AnimatedCurveProps {
  points: Point[];
  color: string;
  strokeWidth: number;
  drawStartFrame: number;
  drawEndFrame: number;
  label: string;
  smooth?: boolean;
  fadeOutStart: number;
  fadeOutEnd: number;
}

/**
 * Convert normalized points to SVG pixel coordinates.
 * x: 0-1 maps to CHART_X..CHART_X+CHART_W
 * y: 0-1 maps from bottom (CHART_Y+CHART_H) to top (CHART_Y) — higher y = higher debt = higher on screen
 */
function toPixel(p: Point): { x: number; y: number } {
  return {
    x: CHART_X + p.x * CHART_W,
    y: CHART_Y + CHART_H * (1 - p.y),
  };
}

/**
 * Generate a smooth Catmull-Rom spline SVG path through points.
 */
function pointsToSmoothPath(points: Point[]): string {
  if (points.length < 2) return "";
  const scaled = points.map(toPixel);

  let d = `M ${scaled[0].x} ${scaled[0].y}`;
  for (let i = 0; i < scaled.length - 1; i++) {
    const p0 = scaled[Math.max(0, i - 1)];
    const p1 = scaled[i];
    const p2 = scaled[i + 1];
    const p3 = scaled[Math.min(scaled.length - 1, i + 2)];

    const tension = 0.3;
    const cp1x = p1.x + (p2.x - p0.x) * tension;
    const cp1y = p1.y + (p2.y - p0.y) * tension;
    const cp2x = p2.x - (p3.x - p1.x) * tension;
    const cp2y = p2.y - (p3.y - p1.y) * tension;

    d += ` C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${p2.x} ${p2.y}`;
  }
  return d;
}

/**
 * Generate a sharp line-segment SVG path (no curves) — for sawtooth generation line.
 */
function pointsToLinearPath(points: Point[]): string {
  if (points.length < 2) return "";
  const scaled = points.map(toPixel);

  let d = `M ${scaled[0].x} ${scaled[0].y}`;
  for (let i = 1; i < scaled.length; i++) {
    d += ` L ${scaled[i].x} ${scaled[i].y}`;
  }
  return d;
}

function estimatePathLength(points: Point[], smooth: boolean): number {
  const scaled = points.map(toPixel);
  let len = 0;
  for (let i = 1; i < scaled.length; i++) {
    const dx = scaled[i].x - scaled[i - 1].x;
    const dy = scaled[i].y - scaled[i - 1].y;
    len += Math.sqrt(dx * dx + dy * dy);
  }
  // Curves are longer than straight segments
  return smooth ? len * 1.2 : len;
}

export const AnimatedCurve: React.FC<AnimatedCurveProps> = ({
  points,
  color,
  strokeWidth,
  drawStartFrame,
  drawEndFrame,
  label,
  smooth = true,
  fadeOutStart,
  fadeOutEnd,
}) => {
  const frame = useCurrentFrame();

  const pathD = useMemo(
    () => (smooth ? pointsToSmoothPath(points) : pointsToLinearPath(points)),
    [points, smooth],
  );
  const pathLength = useMemo(
    () => estimatePathLength(points, smooth),
    [points, smooth],
  );

  const drawProgress = interpolate(
    frame,
    [drawStartFrame, drawEndFrame],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    },
  );

  const dashOffset = pathLength * (1 - drawProgress);

  // Fade out at end
  const opacity = interpolate(
    frame,
    [fadeOutStart, fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    },
  );

  // Label appears after curve drawing begins
  const labelOpacity = interpolate(
    frame,
    [drawEndFrame, drawEndFrame + 20, fadeOutStart, fadeOutEnd],
    [0, 1, 1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    },
  );

  // Label position: right end of line
  const lastPoint = points[points.length - 1];
  const labelPixel = toPixel(lastPoint);

  const glowFilterId = `glow-${label.replace(/\s/g, "")}`;

  if (frame < drawStartFrame) return null;

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <filter id={glowFilterId}>
            <feGaussianBlur stdDeviation="8" />
          </filter>
        </defs>

        {/* Glow layer */}
        <path
          d={pathD}
          fill="none"
          stroke={color}
          strokeWidth={strokeWidth * 3}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={`${pathLength} ${pathLength}`}
          strokeDashoffset={dashOffset}
          opacity={0.25 * opacity}
          filter={`url(#${glowFilterId})`}
        />

        {/* Main line */}
        <path
          d={pathD}
          fill="none"
          stroke={color}
          strokeWidth={strokeWidth}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={`${pathLength} ${pathLength}`}
          strokeDashoffset={dashOffset}
          opacity={opacity}
        />

        {/* Label at line endpoint */}
        <text
          x={labelPixel.x + 12}
          y={labelPixel.y + 6}
          fill={color}
          fontSize={20}
          fontFamily={FONT_FAMILY}
          fontWeight={700}
          opacity={labelOpacity}
        >
          {label}
        </text>
      </svg>
    </AbsoluteFill>
  );
};

export default AnimatedCurve;
