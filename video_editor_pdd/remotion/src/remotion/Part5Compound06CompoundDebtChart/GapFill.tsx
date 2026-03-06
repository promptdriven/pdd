import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate } from "remotion";
import { WIDTH, HEIGHT, CHART_X, CHART_Y, CHART_W, CHART_H } from "./constants";

interface Point {
  x: number;
  y: number;
}

interface GapFillProps {
  topCurve: Point[];
  bottomCurve: Point[];
  fillStartFrame: number;
  fillEndFrame: number;
}

function toPixel(p: Point): { x: number; y: number } {
  return {
    x: CHART_X + p.x * CHART_W,
    y: CHART_Y + CHART_H * (1 - p.y),
  };
}

function sampleCurveAtX(points: Point[], targetX: number): number {
  if (targetX <= points[0].x) return points[0].y;
  if (targetX >= points[points.length - 1].x)
    return points[points.length - 1].y;

  for (let i = 0; i < points.length - 1; i++) {
    if (targetX >= points[i].x && targetX <= points[i + 1].x) {
      const t =
        (targetX - points[i].x) / (points[i + 1].x - points[i].x);
      return points[i].y + t * (points[i + 1].y - points[i].y);
    }
  }
  return points[points.length - 1].y;
}

export const GapFill: React.FC<GapFillProps> = ({
  topCurve,
  bottomCurve,
  fillStartFrame,
  fillEndFrame,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [fillStartFrame, fillEndFrame],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Generate fill polygon up to current progress
  const fillPath = useMemo(() => {
    if (progress <= 0) return "";

    const steps = 60;
    const maxX = progress;
    const topPoints: { x: number; y: number }[] = [];
    const bottomPoints: { x: number; y: number }[] = [];

    for (let i = 0; i <= steps; i++) {
      const x = (i / steps) * maxX;
      const topY = sampleCurveAtX(topCurve, x);
      const bottomY = sampleCurveAtX(bottomCurve, x);
      topPoints.push(toPixel({ x, y: topY }));
      bottomPoints.push(toPixel({ x, y: bottomY }));
    }

    // Build path: top curve forward, then bottom curve backward
    let d = `M ${topPoints[0].x} ${topPoints[0].y}`;
    for (let i = 1; i < topPoints.length; i++) {
      d += ` L ${topPoints[i].x} ${topPoints[i].y}`;
    }
    for (let i = bottomPoints.length - 1; i >= 0; i--) {
      d += ` L ${bottomPoints[i].x} ${bottomPoints[i].y}`;
    }
    d += " Z";

    return d;
  }, [progress, topCurve, bottomCurve]);

  if (frame < fillStartFrame || progress <= 0) return null;

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <linearGradient id="gapGradient" x1="0%" y1="0%" x2="100%" y2="0%">
            <stop
              offset="0%"
              stopColor="rgb(239, 68, 68)"
              stopOpacity={0.04}
            />
            <stop
              offset="100%"
              stopColor="rgb(239, 68, 68)"
              stopOpacity={0.15}
            />
          </linearGradient>
        </defs>

        <path d={fillPath} fill="url(#gapGradient)" />
      </svg>
    </AbsoluteFill>
  );
};

export default GapFill;
