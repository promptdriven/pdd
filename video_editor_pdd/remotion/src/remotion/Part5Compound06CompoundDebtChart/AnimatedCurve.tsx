import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import { WIDTH, HEIGHT, CHART_X, CHART_Y, CHART_W, CHART_H } from "./constants";

interface Point {
  x: number;
  y: number;
}

interface AnimatedCurveProps {
  points: Point[];
  stroke: string;
  strokeWidth: number;
  drawStartFrame: number;
  drawEndFrame: number;
  label: string;
  smooth?: boolean;
}

function pointsToPixels(points: Point[]): { x: number; y: number }[] {
  return points.map((p) => ({
    x: CHART_X + p.x * CHART_W,
    y: CHART_Y + CHART_H * (1 - p.y),
  }));
}

function pointsToSmoothPath(points: Point[]): string {
  if (points.length < 2) return "";

  const scaled = pointsToPixels(points);
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

function pointsToLinearPath(points: Point[]): string {
  if (points.length < 2) return "";

  const scaled = pointsToPixels(points);
  let d = `M ${scaled[0].x} ${scaled[0].y}`;

  for (let i = 1; i < scaled.length; i++) {
    d += ` L ${scaled[i].x} ${scaled[i].y}`;
  }

  return d;
}

function estimatePathLength(points: Point[], smooth: boolean): number {
  const scaled = pointsToPixels(points);
  let len = 0;
  for (let i = 1; i < scaled.length; i++) {
    const dx = scaled[i].x - scaled[i - 1].x;
    const dy = scaled[i].y - scaled[i - 1].y;
    len += Math.sqrt(dx * dx + dy * dy);
  }
  return smooth ? len * 1.2 : len;
}

export const AnimatedCurve: React.FC<AnimatedCurveProps> = ({
  points,
  stroke,
  strokeWidth,
  drawStartFrame,
  drawEndFrame,
  label,
  smooth = true,
}) => {
  const frame = useCurrentFrame();

  const pathD = useMemo(
    () => (smooth ? pointsToSmoothPath(points) : pointsToLinearPath(points)),
    [points, smooth]
  );
  const pathLength = useMemo(
    () => estimatePathLength(points, smooth),
    [points, smooth]
  );

  const drawProgress = interpolate(
    frame,
    [drawStartFrame, drawEndFrame],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.quad),
    }
  );

  const dashOffset = pathLength * (1 - drawProgress);

  // Label appears after line finishes drawing
  const labelOpacity = interpolate(
    frame,
    [drawEndFrame, drawEndFrame + 30],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Label position at end of curve
  const lastPoint = points[points.length - 1];
  const labelX = CHART_X + lastPoint.x * CHART_W + 14;
  const labelY = CHART_Y + CHART_H * (1 - lastPoint.y);

  if (frame < drawStartFrame) return null;

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <path
          d={pathD}
          fill="none"
          stroke={stroke}
          strokeWidth={strokeWidth}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={`${pathLength} ${pathLength}`}
          strokeDashoffset={dashOffset}
        />

        {/* Curve label at endpoint */}
        <text
          x={labelX}
          y={labelY + 6}
          fill={stroke}
          fontSize={20}
          fontFamily="Inter, sans-serif"
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
