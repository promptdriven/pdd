import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import {
  DataPoint,
  MARGIN_LEFT,
  MARGIN_TOP,
  CHART_WIDTH,
  CHART_HEIGHT,
  X_MIN,
  X_MAX,
  Y_MIN,
  Y_MAX,
  LINES_START,
  LINES_DRAW_DURATION,
  LINE_LABEL_OPACITY,
  FONT_FAMILY,
} from './constants';

/** Map data‑space X → pixel X */
const xToPixel = (x: number): number =>
  MARGIN_LEFT + ((x - X_MIN) / (X_MAX - X_MIN)) * CHART_WIDTH;

/** Map data‑space Y → pixel Y */
const yToPixel = (y: number): number =>
  MARGIN_TOP + ((Y_MAX - y) / (Y_MAX - Y_MIN)) * CHART_HEIGHT;

/** Linearly interpolate between data points at a given x */
const interpolateData = (data: DataPoint[], x: number): number => {
  if (x <= data[0].x) return data[0].y;
  if (x >= data[data.length - 1].x) return data[data.length - 1].y;
  for (let i = 0; i < data.length - 1; i++) {
    const a = data[i];
    const b = data[i + 1];
    if (x >= a.x && x <= b.x) {
      const t = (x - a.x) / (b.x - a.x);
      return a.y + t * (b.y - a.y);
    }
  }
  return data[data.length - 1].y;
};

interface AnimatedLineProps {
  data: DataPoint[];
  color: string;
  strokeWidth?: number;
  label: string;
}

export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  data,
  color,
  strokeWidth = 3,
  label,
}) => {
  const frame = useCurrentFrame();

  // Line draw progress: linear over LINES_DRAW_DURATION starting at LINES_START
  const drawProgress = interpolate(
    frame,
    [LINES_START, LINES_START + LINES_DRAW_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  if (drawProgress <= 0) return null;

  // Current x value the line has reached
  const currentX = X_MIN + (X_MAX - X_MIN) * drawProgress;

  // Build the SVG path by sampling every 0.5 year
  const step = 0.5;
  const points: string[] = [];
  for (let x = X_MIN; x <= currentX; x += step) {
    const y = interpolateData(data, x);
    const px = xToPixel(x);
    const py = yToPixel(y);
    points.push(`${px},${py}`);
  }
  // Always include the exact end point
  {
    const y = interpolateData(data, currentX);
    const px = xToPixel(currentX);
    const py = yToPixel(y);
    points.push(`${px},${py}`);
  }

  if (points.length < 2) return null;

  const pathD = `M ${points[0]} ` + points.slice(1).map((p) => `L ${p}`).join(' ');

  // End‑of‑line label (appears when line is 80% drawn)
  const labelOpacity = interpolate(
    drawProgress,
    [0.8, 0.95],
    [0, LINE_LABEL_OPACITY],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  const endY = interpolateData(data, currentX);
  const endPx = xToPixel(currentX);
  const endPy = yToPixel(endY);

  // Position label at 1970 in data-space so it doesn't crowd the right edge
  const labelX = Math.min(currentX, 1970);
  const labelY = interpolateData(data, labelX);
  const labelPx = xToPixel(labelX);
  const labelPy = yToPixel(labelY);

  return (
    <svg
      width={1920}
      height={1080}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
        strokeLinejoin="round"
      />

      {/* Small dot at the current tip */}
      <circle cx={endPx} cy={endPy} r={4} fill={color} />

      {/* Label positioned inward from the right edge */}
      {labelOpacity > 0.01 && (
        <text
          x={labelPx}
          y={labelPy - 14}
          textAnchor="end"
          fill={color}
          fillOpacity={labelOpacity}
          fontFamily={FONT_FAMILY}
          fontSize={12}
        >
          {label}
        </text>
      )}
    </svg>
  );
};

/** Export helper for other sub‑components to sample line data */
export { interpolateData };

export default AnimatedLine;
