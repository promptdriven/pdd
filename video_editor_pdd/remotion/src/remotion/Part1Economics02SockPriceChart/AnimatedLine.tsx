import React from "react";
import { useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CHART_LEFT,
  CHART_TOP,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
  LINE_STROKE_WIDTH,
  LINES_DRAW_START,
  LINES_DRAW_END,
} from "./constants";

type DataPoint = { x: number; y: number };

interface AnimatedLineProps {
  data: DataPoint[];
  color: string;
  strokeWidth?: number;
  fadeOutStart?: number;
  fadeOutEnd?: number;
}

/**
 * Convert data coordinates to SVG pixel coordinates within the chart area.
 */
const toPixel = (
  pt: DataPoint
): { px: number; py: number } => ({
  px: ((pt.x - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH,
  py: CHART_HEIGHT - ((pt.y - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT,
});

/**
 * Build a smooth SVG path using monotone cubic interpolation.
 */
const buildSmoothPath = (data: DataPoint[]): string => {
  if (data.length < 2) return "";
  const pixels = data.map(toPixel);

  // Catmull-Rom to Bezier for smooth monotone curves
  const segments: string[] = [`M ${pixels[0].px} ${pixels[0].py}`];

  for (let i = 0; i < pixels.length - 1; i++) {
    const p0 = pixels[Math.max(0, i - 1)];
    const p1 = pixels[i];
    const p2 = pixels[i + 1];
    const p3 = pixels[Math.min(pixels.length - 1, i + 2)];

    const tension = 0.35;
    const cp1x = p1.px + (p2.px - p0.px) * tension;
    const cp1y = p1.py + (p2.py - p0.py) * tension;
    const cp2x = p2.px - (p3.px - p1.px) * tension;
    const cp2y = p2.py - (p3.py - p1.py) * tension;

    segments.push(
      `C ${cp1x.toFixed(1)} ${cp1y.toFixed(1)}, ${cp2x.toFixed(1)} ${cp2y.toFixed(1)}, ${p2.px.toFixed(1)} ${p2.py.toFixed(1)}`
    );
  }

  return segments.join(" ");
};

/**
 * Compute approximate total path length for the smooth path (using line segments).
 */
const computePathLength = (data: DataPoint[]): number => {
  const pixels = data.map(toPixel);
  let len = 0;
  for (let i = 1; i < pixels.length; i++) {
    const dx = pixels[i].px - pixels[i - 1].px;
    const dy = pixels[i].py - pixels[i - 1].py;
    len += Math.sqrt(dx * dx + dy * dy);
  }
  // Curves are longer than straight segments; approximate with 1.15x multiplier
  return len * 1.15;
};

export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  data,
  color,
  strokeWidth = LINE_STROKE_WIDTH,
  fadeOutStart,
  fadeOutEnd,
}) => {
  const frame = useCurrentFrame();

  const drawProgress = interpolate(
    frame,
    [LINES_DRAW_START, LINES_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.inOut(Easing.cubic),
    }
  );

  const opacity =
    fadeOutStart !== undefined && fadeOutEnd !== undefined
      ? interpolate(frame, [fadeOutStart, fadeOutEnd], [1, 0], {
          extrapolateLeft: "clamp",
          extrapolateRight: "clamp",
        })
      : 1;

  const pathD = buildSmoothPath(data);
  const totalLength = computePathLength(data);
  const visibleLength = totalLength * drawProgress;
  const hiddenLength = totalLength - visibleLength;

  return (
    <svg
      width={CHART_WIDTH}
      height={CHART_HEIGHT}
      viewBox={`0 0 ${CHART_WIDTH} ${CHART_HEIGHT}`}
      style={{
        position: "absolute",
        left: CHART_LEFT,
        top: CHART_TOP,
        overflow: "visible",
        opacity,
      }}
    >
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={`${totalLength}`}
        strokeDashoffset={hiddenLength}
      />
      {/* Glowing halo behind the line */}
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth + 6}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={`${totalLength}`}
        strokeDashoffset={hiddenLength}
        opacity={0.15}
        filter="url(#lineGlow)"
      />
      <defs>
        <filter id="lineGlow" x="-50%" y="-50%" width="200%" height="200%">
          <feGaussianBlur stdDeviation="6" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>
    </svg>
  );
};

export default AnimatedLine;
