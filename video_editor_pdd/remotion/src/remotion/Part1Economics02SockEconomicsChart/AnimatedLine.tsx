import React from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  MARGIN_LEFT,
  MARGIN_TOP,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
  LINE_STROKE_WIDTH,
  LINE_LABEL_SIZE,
  LINES_DRAW_START,
  LINES_DRAW_END,
  LINE_LABELS_FADE_START,
  LINE_LABELS_FADE_END,
} from "./constants";

/** Map data x to pixel x */
const xToPixel = (x: number): number =>
  MARGIN_LEFT + ((x - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;

/** Map data y to pixel y */
const yToPixel = (y: number): number =>
  MARGIN_TOP + CHART_HEIGHT - ((y - Y_MIN) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;

/** Linearly interpolate between two data points */
const lerpData = (
  data: { x: number; y: number }[],
  targetX: number
): number => {
  if (targetX <= data[0].x) return data[0].y;
  if (targetX >= data[data.length - 1].x) return data[data.length - 1].y;
  for (let i = 0; i < data.length - 1; i++) {
    if (targetX >= data[i].x && targetX <= data[i + 1].x) {
      const t = (targetX - data[i].x) / (data[i + 1].x - data[i].x);
      return data[i].y + t * (data[i + 1].y - data[i].y);
    }
  }
  return data[data.length - 1].y;
};

interface AnimatedLineProps {
  data: { x: number; y: number }[];
  color: string;
  label: string;
}

export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  data,
  color,
  label,
}) => {
  const frame = useCurrentFrame();

  // Current X position based on animation progress (linear draw)
  const drawProgress = interpolate(
    frame,
    [LINES_DRAW_START, LINES_DRAW_END],
    [0, 1],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  const currentMaxX = X_MIN + (X_MAX - X_MIN) * drawProgress;

  // Label fade in at end of draw
  const labelOpacity = interpolate(
    frame,
    [LINE_LABELS_FADE_START, LINE_LABELS_FADE_END],
    [0, 0.7],
    { extrapolateLeft: "clamp", extrapolateRight: "clamp" }
  );

  // Build visible path points — sample every 0.5 years for smoothness
  const pathPoints: { px: number; py: number }[] = [];
  const step = 0.5;
  for (let x = X_MIN; x <= Math.min(currentMaxX, X_MAX); x += step) {
    const y = lerpData(data, x);
    pathPoints.push({ px: xToPixel(x), py: yToPixel(y) });
  }
  // Ensure we include the exact currentMaxX endpoint
  if (currentMaxX <= X_MAX) {
    const y = lerpData(data, currentMaxX);
    pathPoints.push({ px: xToPixel(currentMaxX), py: yToPixel(y) });
  }

  if (pathPoints.length < 2) return null;

  // Build SVG path
  const d = pathPoints
    .map((p, i) => `${i === 0 ? "M" : "L"} ${p.px} ${p.py}`)
    .join(" ");

  // Last visible point for label positioning
  const lastPoint = pathPoints[pathPoints.length - 1];

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
        strokeWidth={LINE_STROKE_WIDTH}
        strokeLinecap="round"
        strokeLinejoin="round"
      />

      {/* Line label at the end */}
      {labelOpacity > 0 && (
        <text
          x={lastPoint.px + 10}
          y={lastPoint.py - 10}
          fill={color}
          fillOpacity={labelOpacity}
          fontSize={LINE_LABEL_SIZE}
          fontFamily="'Inter', sans-serif"
        >
          {label}
        </text>
      )}
    </svg>
  );
};

export default AnimatedLine;
