import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { GRAPH_AREA, DIMENSIONS, DATA } from './constants';

interface AnimatedLineSeriesProps {
  data: number[];
  color: string;
  strokeWidth: number;
  glowRadius: number;
  startFrame: number;
  duration: number;
}

export const AnimatedLineSeries: React.FC<AnimatedLineSeriesProps> = ({
  data,
  color,
  strokeWidth,
  glowRadius,
  startFrame,
  duration,
}) => {
  const frame = useCurrentFrame();

  const progress = interpolate(
    frame,
    [startFrame, startFrame + duration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    }
  );

  // Convert data points to SVG coordinates
  const points = data.map((value, i) => {
    const x = GRAPH_AREA.left + (i / (data.length - 1)) * DIMENSIONS.graphWidth;
    const y =
      GRAPH_AREA.bottom -
      ((value - DATA.yMin) / (DATA.yMax - DATA.yMin)) * DIMENSIONS.graphHeight;
    return { x, y };
  });

  // Create path data
  const pathData = points
    .map((point, i) => {
      if (i === 0) {
        return `M ${point.x} ${point.y}`;
      }
      return `L ${point.x} ${point.y}`;
    })
    .join(' ');

  // Calculate total path length (approximate)
  let totalLength = 0;
  for (let i = 1; i < points.length; i++) {
    const dx = points[i].x - points[i - 1].x;
    const dy = points[i].y - points[i - 1].y;
    totalLength += Math.sqrt(dx * dx + dy * dy);
  }

  const dashOffset = totalLength * (1 - progress);

  // Create gradient fill path
  const fillPathData =
    pathData +
    ` L ${points[points.length - 1].x} ${GRAPH_AREA.bottom}` +
    ` L ${points[0].x} ${GRAPH_AREA.bottom} Z`;

  // Determine which points to show based on progress
  const visiblePointCount = Math.floor(progress * data.length);

  return (
    <svg
      width={DIMENSIONS.canvasWidth}
      height={DIMENSIONS.canvasHeight}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <linearGradient id={`gradient-${color}`} x1="0%" y1="0%" x2="0%" y2="100%">
          <stop offset="0%" stopColor={color} stopOpacity={0.5} />
          <stop offset="100%" stopColor={color} stopOpacity={0} />
        </linearGradient>
        <filter id={`glow-${color}`}>
          <feGaussianBlur stdDeviation={glowRadius / 2} result="coloredBlur" />
          <feMerge>
            <feMergeNode in="coloredBlur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Gradient fill */}
      {progress > 0 && (
        <path
          d={fillPathData}
          fill={`url(#gradient-${color})`}
          opacity={progress}
        />
      )}

      {/* Line with glow */}
      <path
        d={pathData}
        fill="none"
        stroke={color}
        strokeWidth={strokeWidth}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={totalLength}
        strokeDashoffset={dashOffset}
        filter={`url(#glow-${color})`}
      />

      {/* Point markers */}
      {points.map((point, i) => {
        if (i > visiblePointCount) return null;

        const pointProgress = interpolate(
          frame,
          [startFrame + (i / data.length) * duration, startFrame + (i / data.length) * duration + 10],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.back(1.5)),
          }
        );

        const scale = pointProgress;

        return (
          <circle
            key={i}
            cx={point.x}
            cy={point.y}
            r={8 * scale}
            fill={color}
            opacity={pointProgress}
          />
        );
      })}
    </svg>
  );
};
