import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { CHART, TIMING, pointsToPath } from './constants';

interface AnimatedCurveProps {
  points: [number, number][];
  color: string;
  label: string;
  glowBlur?: number;
  glowOpacity?: number;
}

export const AnimatedCurve: React.FC<AnimatedCurveProps> = ({
  points,
  color,
  label,
  glowBlur = 8,
  glowOpacity = 0.1,
}) => {
  const frame = useCurrentFrame();

  const localFrame = frame - TIMING.curvesStart;
  const drawProgress = interpolate(
    localFrame,
    [0, TIMING.curvesDuration],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.inOut(Easing.cubic) }
  );

  // Label appears after gap fill starts (frame 180)
  const labelOpacity = interpolate(
    frame,
    [TIMING.gapFillStart, TIMING.gapFillStart + 30],
    [0, 1],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  if (localFrame < 0) return null;

  const pathD = pointsToPath(points);
  const filterId = `glow-${color.replace('#', '')}`;

  // Calculate endpoint position based on draw progress
  const endPoint = getPointAtProgress(points, drawProgress);

  return (
    <svg
      width={CHART.width}
      height={CHART.height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <filter id={filterId}>
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
        strokeWidth={3.5}
        opacity={glowOpacity}
        filter={`url(#${filterId})`}
        strokeDasharray={getTotalLength(points)}
        strokeDashoffset={getTotalLength(points) * (1 - drawProgress)}
        strokeLinecap="round"
        strokeLinejoin="round"
      />

      {/* Main curve */}
      <path
        d={pathD}
        fill="none"
        stroke={color}
        strokeWidth={3.5}
        strokeDasharray={getTotalLength(points)}
        strokeDashoffset={getTotalLength(points) * (1 - drawProgress)}
        strokeLinecap="round"
        strokeLinejoin="round"
      />

      {/* Animated endpoint dot */}
      {drawProgress > 0 && drawProgress < 1 && (
        <circle
          cx={endPoint[0]}
          cy={endPoint[1]}
          r={4}
          fill={color}
          opacity={0.8}
        />
      )}

      {/* Endpoint label */}
      {labelOpacity > 0 && (
        <text
          x={points[points.length - 1][0] + 12}
          y={points[points.length - 1][1] + 5}
          fontFamily="Inter, sans-serif"
          fontSize={16}
          fontWeight={700}
          fill={color}
          opacity={labelOpacity}
        >
          {label}
        </text>
      )}
    </svg>
  );
};

// Approximate total path length for dash animation
function getTotalLength(points: [number, number][]): number {
  let length = 0;
  for (let i = 1; i < points.length; i++) {
    const dx = points[i][0] - points[i - 1][0];
    const dy = points[i][1] - points[i - 1][1];
    length += Math.sqrt(dx * dx + dy * dy);
  }
  // Bezier curves are longer than straight lines; approximate with 1.3x
  return length * 1.3;
}

// Get point at a given progress along the polyline
function getPointAtProgress(
  points: [number, number][],
  progress: number
): [number, number] {
  if (progress <= 0) return points[0];
  if (progress >= 1) return points[points.length - 1];

  const totalLen = getTotalLength(points) / 1.3; // Use straight-line total
  const targetLen = totalLen * progress;

  let accumulated = 0;
  for (let i = 1; i < points.length; i++) {
    const dx = points[i][0] - points[i - 1][0];
    const dy = points[i][1] - points[i - 1][1];
    const segLen = Math.sqrt(dx * dx + dy * dy);
    if (accumulated + segLen >= targetLen) {
      const t = (targetLen - accumulated) / segLen;
      return [
        points[i - 1][0] + dx * t,
        points[i - 1][1] + dy * t,
      ];
    }
    accumulated += segLen;
  }
  return points[points.length - 1];
}
