// AnimatedLine.tsx — Draws a polyline that progressively reveals via stroke-dashoffset
import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";

interface AnimatedLineProps {
  /** Array of [x, y] coordinate pairs */
  points: Array<[number, number]>;
  /** Stroke color */
  color: string;
  /** Stroke width */
  strokeWidth: number;
  /** Whether the line should be dashed */
  dashed?: boolean;
  /** Frame at which drawing begins (absolute frame number) */
  drawStartFrame: number;
  /** Number of frames over which the line draws in */
  drawDuration: number;
  /** Whether to use easeIn(quad) for drawing (default true) */
  easeInDraw?: boolean;
  /** If provided, only show this many points (for static partial display) */
  staticPointCount?: number;
}

function pointsToPathD(pts: Array<[number, number]>): string {
  if (pts.length === 0) return "";
  return pts
    .map((p, i) => `${i === 0 ? "M" : "L"} ${p[0]} ${p[1]}`)
    .join(" ");
}

function computeTotalLength(pts: Array<[number, number]>): number {
  let total = 0;
  for (let i = 1; i < pts.length; i++) {
    const dx = pts[i][0] - pts[i - 1][0];
    const dy = pts[i][1] - pts[i - 1][1];
    total += Math.sqrt(dx * dx + dy * dy);
  }
  return total;
}

export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  points,
  color,
  strokeWidth,
  dashed = false,
  drawStartFrame,
  drawDuration,
  easeInDraw = true,
  staticPointCount,
}) => {
  const frame = useCurrentFrame();

  const displayPoints =
    staticPointCount !== undefined
      ? points.slice(0, staticPointCount)
      : points;

  if (displayPoints.length < 2) return null;

  const d = pointsToPathD(displayPoints);
  const totalLength = computeTotalLength(displayPoints);

  // If staticPointCount is set and no animation, just render fully
  if (staticPointCount !== undefined && drawDuration === 0) {
    return (
      <svg
        width={1920}
        height={1080}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        <path
          d={d}
          fill="none"
          stroke={color}
          strokeWidth={strokeWidth}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={dashed ? "12 8" : "none"}
        />
      </svg>
    );
  }

  // Animated draw-in progress
  const progress = interpolate(
    frame,
    [drawStartFrame, drawStartFrame + drawDuration],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: easeInDraw ? Easing.in(Easing.quad) : Easing.linear,
    }
  );

  const dashOffset = totalLength * (1 - progress);

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: "absolute", top: 0, left: 0 }}
    >
      <path
        d={d}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={
          dashed ? `12 8` : `${totalLength}`
        }
        strokeDashoffset={dashed ? 0 : dashOffset}
        opacity={progress > 0 || staticPointCount !== undefined ? 1 : 0}
      />
    </svg>
  );
};
