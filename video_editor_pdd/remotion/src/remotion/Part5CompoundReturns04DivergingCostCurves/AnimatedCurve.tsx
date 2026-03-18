import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { WIDTH, HEIGHT, CURVES_START, CURVES_DURATION, LABELS_START } from './constants';

/**
 * Attempt to build a smooth cubic Bezier SVG path through a set of points.
 * Uses Catmull-Rom → cubic Bezier conversion for smooth interpolation.
 */
function buildSmoothPath(points: [number, number][]): string {
  if (points.length < 2) return '';
  if (points.length === 2) {
    return `M${points[0][0]},${points[0][1]} L${points[1][0]},${points[1][1]}`;
  }

  let d = `M${points[0][0]},${points[0][1]}`;

  for (let i = 0; i < points.length - 1; i++) {
    const p0 = points[Math.max(0, i - 1)];
    const p1 = points[i];
    const p2 = points[i + 1];
    const p3 = points[Math.min(points.length - 1, i + 2)];

    const tension = 0.3;
    const cp1x = p1[0] + (p2[0] - p0[0]) * tension;
    const cp1y = p1[1] + (p2[1] - p0[1]) * tension;
    const cp2x = p2[0] - (p3[0] - p1[0]) * tension;
    const cp2y = p2[1] - (p3[1] - p1[1]) * tension;

    d += ` C${cp1x},${cp1y} ${cp2x},${cp2y} ${p2[0]},${p2[1]}`;
  }

  return d;
}

/** Compute total length of a polyline approximation. */
function polylineLength(points: [number, number][]): number {
  let total = 0;
  for (let i = 1; i < points.length; i++) {
    const dx = points[i][0] - points[i - 1][0];
    const dy = points[i][1] - points[i - 1][1];
    total += Math.sqrt(dx * dx + dy * dy);
  }
  return total;
}

interface AnimatedCurveProps {
  points: [number, number][];
  color: string;
  label: string;
  strokeWidth?: number;
  glowBlur?: number;
}

export const AnimatedCurve: React.FC<AnimatedCurveProps> = ({
  points,
  color,
  label,
  strokeWidth = 3.5,
  glowBlur = 8,
}) => {
  const frame = useCurrentFrame();

  const pathD = useMemo(() => buildSmoothPath(points), [points]);
  const totalLen = useMemo(() => polylineLength(points) * 1.2, [points]); // approximate

  // Draw progress: 0→1 over CURVES_DURATION, starting at CURVES_START
  const drawProgress = interpolate(
    frame,
    [CURVES_START, CURVES_START + CURVES_DURATION],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  // Endpoint label fades in at LABELS_START
  const labelOpacity = interpolate(
    frame,
    [LABELS_START, LABELS_START + 20],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  const dashOffset = totalLen * (1 - drawProgress);
  const endPoint = points[points.length - 1];

  // Label position: slightly to the right of the end point
  const labelX = endPoint[0] + 12;
  const labelY = endPoint[1] + 5;

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <filter id={`glow-${color.replace('#', '')}`}>
          <feGaussianBlur stdDeviation={glowBlur} result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Glow layer */}
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth + 4}
        strokeLinecap="round"
        strokeLinejoin="round"
        opacity={0.1}
        strokeDasharray={totalLen}
        strokeDashoffset={dashOffset}
        filter={`url(#glow-${color.replace('#', '')})`}
      />

      {/* Main curve */}
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={totalLen}
        strokeDashoffset={dashOffset}
      />

      {/* Endpoint label */}
      <text
        x={labelX}
        y={labelY}
        fill={color}
        opacity={labelOpacity}
        fontFamily="Inter, sans-serif"
        fontSize={16}
        fontWeight={700}
      >
        {label}
      </text>
    </svg>
  );
};
