import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  WIDTH,
  HEIGHT,
  FONT_FAMILY,
  dataToPixelX,
  dataToPixelY,
} from "./constants";

interface DataPoint {
  x: number;
  y: number;
}

interface AnimatedLineProps {
  data: DataPoint[];
  color: string;
  strokeWidth: number;
  drawStartFrame: number;
  drawEndFrame: number;
  dashed?: boolean;
  dashArray?: string;
  label: string;
  labelOpacityMultiplier?: number;
}

/** Convert data points to a smooth cubic Bézier SVG path. */
function dataToSmoothPath(data: DataPoint[]): string {
  if (data.length < 2) return "";

  const pts = data.map((d) => ({
    x: dataToPixelX(d.x),
    y: dataToPixelY(d.y),
  }));

  let d = `M ${pts[0].x} ${pts[0].y}`;
  const tension = 0.3;

  for (let i = 0; i < pts.length - 1; i++) {
    const p0 = pts[Math.max(0, i - 1)];
    const p1 = pts[i];
    const p2 = pts[i + 1];
    const p3 = pts[Math.min(pts.length - 1, i + 2)];

    const cp1x = p1.x + (p2.x - p0.x) * tension;
    const cp1y = p1.y + (p2.y - p0.y) * tension;
    const cp2x = p2.x - (p3.x - p1.x) * tension;
    const cp2y = p2.y - (p3.y - p1.y) * tension;

    d += ` C ${cp1x} ${cp1y}, ${cp2x} ${cp2y}, ${p2.x} ${p2.y}`;
  }

  return d;
}

/** Estimate polyline length (scaled up for curves). */
function estimatePathLength(data: DataPoint[]): number {
  const pts = data.map((d) => ({
    x: dataToPixelX(d.x),
    y: dataToPixelY(d.y),
  }));
  let len = 0;
  for (let i = 1; i < pts.length; i++) {
    const dx = pts[i].x - pts[i - 1].x;
    const dy = pts[i].y - pts[i - 1].y;
    len += Math.sqrt(dx * dx + dy * dy);
  }
  return len * 1.2;
}

export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  data,
  color,
  strokeWidth,
  drawStartFrame,
  drawEndFrame,
  dashed = false,
  dashArray = "8 4",
  label,
  labelOpacityMultiplier = 0.7,
}) => {
  const frame = useCurrentFrame();

  const pathD = useMemo(() => dataToSmoothPath(data), [data]);
  const pathLength = useMemo(() => estimatePathLength(data), [data]);

  // Draw progress: line draws left-to-right
  const drawProgress = interpolate(
    frame,
    [drawStartFrame, drawEndFrame],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // For dashed lines, fade in; for solid lines, use strokeDashoffset draw
  const lineOpacity = dashed
    ? interpolate(frame, [drawStartFrame, drawEndFrame], [0, 1], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
      })
    : 1;

  const dashOffset = dashed ? 0 : pathLength * (1 - drawProgress);

  // Label fades in after line is drawn
  const labelFadeOpacity = interpolate(
    frame,
    [drawEndFrame, drawEndFrame + 30],
    [0, labelOpacityMultiplier],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    }
  );

  // Label position: right end of the line
  const lastPt = data[data.length - 1];
  const labelX = dataToPixelX(lastPt.x) + 14;
  const labelY = dataToPixelY(lastPt.y);

  const glowId = `glow-${label.replace(/\s/g, "-")}`;

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
          {!dashed && (
            <filter id={glowId}>
              <feGaussianBlur stdDeviation="6" />
            </filter>
          )}
        </defs>

        {/* Glow layer (solid lines only) */}
        {!dashed && (
          <path
            d={pathD}
            fill="none"
            stroke={color}
            strokeWidth={strokeWidth * 3}
            strokeLinecap="round"
            strokeLinejoin="round"
            strokeDasharray={`${pathLength} ${pathLength}`}
            strokeDashoffset={dashOffset}
            opacity={0.2 * lineOpacity}
            filter={`url(#${glowId})`}
          />
        )}

        {/* Main line */}
        <path
          d={pathD}
          fill="none"
          stroke={color}
          strokeWidth={strokeWidth}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={
            dashed ? dashArray : `${pathLength} ${pathLength}`
          }
          strokeDashoffset={dashed ? 0 : dashOffset}
          opacity={lineOpacity}
        />

        {/* Label */}
        <text
          x={labelX}
          y={labelY + 5}
          fill={color}
          fontSize={12}
          fontFamily={FONT_FAMILY}
          fontWeight={500}
          opacity={labelFadeOpacity}
        >
          {label}
        </text>
      </svg>
    </AbsoluteFill>
  );
};

export default AnimatedLine;
