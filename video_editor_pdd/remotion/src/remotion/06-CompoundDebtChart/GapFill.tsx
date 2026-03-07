import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";

const WIDTH = 1920;
const HEIGHT = 1080;
const CHART_X = 200;
const CHART_Y = 80;
const CHART_W = 1620;
const CHART_H = 800;

interface Point {
  x: number;
  y: number;
}

interface GapFillProps {
  topCurve: Point[];
  bottomCurve: Point[];
  fillStartFrame: number;
  fillEndFrame: number;
  fadeOutStart: number;
  fadeOutEnd: number;
}

function toPixel(p: Point): { x: number; y: number } {
  return {
    x: CHART_X + p.x * CHART_W,
    y: CHART_Y + CHART_H * (1 - p.y),
  };
}

/**
 * Sample a curve at a given normalized x (0-1) using linear interpolation between points.
 */
function sampleCurveY(points: Point[], xNorm: number): number {
  if (xNorm <= points[0].x) return points[0].y;
  if (xNorm >= points[points.length - 1].x) return points[points.length - 1].y;

  for (let i = 0; i < points.length - 1; i++) {
    if (xNorm >= points[i].x && xNorm <= points[i + 1].x) {
      const t = (xNorm - points[i].x) / (points[i + 1].x - points[i].x);
      return points[i].y + t * (points[i + 1].y - points[i].y);
    }
  }
  return points[points.length - 1].y;
}

/**
 * Build a closed polygon path between two curves for the fill area.
 * Samples at regular intervals for smooth fill shape.
 */
function buildFillPath(topCurve: Point[], bottomCurve: Point[], progress: number): string {
  const numSamples = 60;
  const maxX = progress; // progress 0-1 determines how far right we fill

  if (maxX <= 0) return "";

  const topPoints: { x: number; y: number }[] = [];
  const bottomPoints: { x: number; y: number }[] = [];

  for (let i = 0; i <= numSamples; i++) {
    const xNorm = (i / numSamples) * maxX;
    const topY = sampleCurveY(topCurve, xNorm);
    const bottomY = sampleCurveY(bottomCurve, xNorm);
    topPoints.push(toPixel({ x: xNorm, y: topY }));
    bottomPoints.push(toPixel({ x: xNorm, y: bottomY }));
  }

  // Build path: top curve left-to-right, then bottom curve right-to-left
  let d = `M ${topPoints[0].x} ${topPoints[0].y}`;
  for (let i = 1; i < topPoints.length; i++) {
    d += ` L ${topPoints[i].x} ${topPoints[i].y}`;
  }
  for (let i = bottomPoints.length - 1; i >= 0; i--) {
    d += ` L ${bottomPoints[i].x} ${bottomPoints[i].y}`;
  }
  d += " Z";

  return d;
}

export const GapFill: React.FC<GapFillProps> = ({
  topCurve,
  bottomCurve,
  fillStartFrame,
  fillEndFrame,
  fadeOutStart,
  fadeOutEnd,
}) => {
  const frame = useCurrentFrame();

  const fillProgress = interpolate(
    frame,
    [fillStartFrame, fillEndFrame],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    },
  );

  const fadeOutOpacity = interpolate(
    frame,
    [fadeOutStart, fadeOutEnd],
    [1, 0],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.in(Easing.cubic),
    },
  );

  const fillPath = useMemo(
    () => buildFillPath(topCurve, bottomCurve, fillProgress),
    [topCurve, bottomCurve, fillProgress],
  );

  if (frame < fillStartFrame || !fillPath) return null;

  const gradientId = "gapFillGradient";

  return (
    <AbsoluteFill>
      <svg
        width={WIDTH}
        height={HEIGHT}
        viewBox={`0 0 ${WIDTH} ${HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <defs>
          <linearGradient id={gradientId} x1="0%" y1="0%" x2="100%" y2="0%">
            <stop offset="0%" stopColor="rgba(239, 68, 68, 0.04)" />
            <stop offset="100%" stopColor="rgba(239, 68, 68, 0.15)" />
          </linearGradient>
        </defs>

        <path
          d={fillPath}
          fill={`url(#${gradientId})`}
          opacity={fadeOutOpacity}
        />
      </svg>
    </AbsoluteFill>
  );
};

export default GapFill;
