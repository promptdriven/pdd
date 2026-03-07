import React, { useMemo } from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import { WIDTH, HEIGHT, CHART_X, CHART_Y, CHART_W, CHART_H, FONT_FAMILY } from "./constants";

interface Point {
  x: number;
  y: number;
}

interface AnimatedLineProps {
  points: Point[];
  gradientId: string;
  colorStart: string;
  colorEnd: string;
  strokeWidth: number;
  drawStartFrame: number;
  drawEndFrame: number;
  dashed?: boolean;
  maxOpacity?: number;
  label: string;
  labelColor: string;
}

function pointsToSmoothPath(points: Point[]): string {
  if (points.length < 2) return "";

  const scaled = points.map((p) => ({
    x: CHART_X + p.x * CHART_W,
    y: CHART_Y + CHART_H * (1 - p.y),
  }));

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

function estimatePathLength(points: Point[]): number {
  const scaled = points.map((p) => ({
    x: CHART_X + p.x * CHART_W,
    y: CHART_Y + CHART_H * (1 - p.y),
  }));
  let len = 0;
  for (let i = 1; i < scaled.length; i++) {
    const dx = scaled[i].x - scaled[i - 1].x;
    const dy = scaled[i].y - scaled[i - 1].y;
    len += Math.sqrt(dx * dx + dy * dy);
  }
  // Curves are longer than straight segments — scale up estimate
  return len * 1.2;
}

export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  points,
  gradientId,
  colorStart,
  colorEnd,
  strokeWidth,
  drawStartFrame,
  drawEndFrame,
  dashed,
  maxOpacity = 1,
  label,
  labelColor,
}) => {
  const frame = useCurrentFrame();

  const pathD = useMemo(() => pointsToSmoothPath(points), [points]);
  const pathLength = useMemo(() => estimatePathLength(points), [points]);

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

  // For dashed total-cost line, fade opacity instead of draw-in
  const opacity = dashed
    ? interpolate(frame, [drawStartFrame, drawEndFrame], [0, maxOpacity], {
        extrapolateLeft: "clamp",
        extrapolateRight: "clamp",
      })
    : maxOpacity;

  const dashOffset = dashed ? 0 : pathLength * (1 - drawProgress);

  // Label appears after line is fully drawn
  const labelOpacity = interpolate(
    frame,
    [drawEndFrame, drawEndFrame + 30],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    },
  );

  // Label position: right end of line
  const lastPoint = points[points.length - 1];
  const labelX = CHART_X + lastPoint.x * CHART_W + 12;
  const labelY = CHART_Y + CHART_H * (1 - lastPoint.y);

  const glowFilterId = `${gradientId}Glow`;

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
          <linearGradient id={gradientId} x1="0%" y1="0%" x2="100%" y2="0%">
            <stop offset="0%" stopColor={colorStart} />
            <stop offset="100%" stopColor={colorEnd} />
          </linearGradient>
          {!dashed && (
            <filter id={glowFilterId}>
              <feGaussianBlur stdDeviation="8" />
            </filter>
          )}
        </defs>

        {/* Glow layer under the main line (non-dashed lines only) */}
        {!dashed && (
          <path
            d={pathD}
            fill="none"
            stroke={`url(#${gradientId})`}
            strokeWidth={strokeWidth * 3}
            strokeLinecap="round"
            strokeLinejoin="round"
            strokeDasharray={`${pathLength} ${pathLength}`}
            strokeDashoffset={dashOffset}
            opacity={0.25 * opacity}
            filter={`url(#${glowFilterId})`}
          />
        )}

        {/* Main line */}
        <path
          d={pathD}
          fill="none"
          stroke={dashed ? colorStart : `url(#${gradientId})`}
          strokeWidth={strokeWidth}
          strokeLinecap="round"
          strokeLinejoin="round"
          strokeDasharray={
            dashed ? "8 6" : `${pathLength} ${pathLength}`
          }
          strokeDashoffset={dashed ? 0 : dashOffset}
          opacity={opacity}
        />

        {/* Label at line endpoint */}
        <text
          x={labelX}
          y={labelY + 6}
          fill={labelColor}
          fontSize={22}
          fontFamily={FONT_FAMILY}
          fontWeight={600}
          opacity={labelOpacity}
        >
          {label}
        </text>
      </svg>
    </AbsoluteFill>
  );
};

export default AnimatedLine;
