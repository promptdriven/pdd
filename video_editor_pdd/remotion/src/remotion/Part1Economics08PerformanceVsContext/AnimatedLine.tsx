import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  LINE_COLOR,
  PERFORMANCE_DATA,
  PHASE_LINE_DRAW_START,
  PHASE_LINE_DRAW_END,
  CHART_PADDING_LEFT,
  CHART_PADDING_RIGHT,
  CHART_PADDING_TOP,
  CHART_PADDING_BOTTOM,
} from './constants';

interface AnimatedLineProps {
  chartWidth: number;
  chartHeight: number;
}

/**
 * Draws the declining performance line with animated stroke-dashoffset.
 * Also renders data-point circles that appear as the line reaches them.
 */
export const AnimatedLine: React.FC<AnimatedLineProps> = ({
  chartWidth,
  chartHeight,
}) => {
  const frame = useCurrentFrame();

  const plotLeft = CHART_PADDING_LEFT;
  const plotRight = chartWidth - CHART_PADDING_RIGHT;
  const plotTop = CHART_PADDING_TOP;
  const plotBottom = chartHeight - CHART_PADDING_BOTTOM;
  const plotW = plotRight - plotLeft;
  const plotH = plotBottom - plotTop;

  // Map data to chart coordinates
  const points = PERFORMANCE_DATA.map((d, i) => ({
    x: plotLeft + (i / (PERFORMANCE_DATA.length - 1)) * plotW,
    y: plotTop + (1 - d.value) * plotH,
    label: d.label,
    value: d.value,
  }));

  // Build SVG path
  const pathD = points
    .map((p, i) => `${i === 0 ? 'M' : 'L'} ${p.x} ${p.y}`)
    .join(' ');

  // Approximate total path length for dash animation
  let totalLength = 0;
  for (let i = 1; i < points.length; i++) {
    const dx = points[i].x - points[i - 1].x;
    const dy = points[i].y - points[i - 1].y;
    totalLength += Math.sqrt(dx * dx + dy * dy);
  }

  // Draw progress: 0 → 1
  const drawProgress = interpolate(
    frame,
    [PHASE_LINE_DRAW_START, PHASE_LINE_DRAW_END],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.inOut(Easing.cubic),
    },
  );

  const dashOffset = totalLength * (1 - drawProgress);

  return (
    <svg
      width={chartWidth}
      height={chartHeight}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* Gradient glow behind the line */}
      <defs>
        <filter id="lineGlow" x="-20%" y="-20%" width="140%" height="140%">
          <feGaussianBlur stdDeviation="4" result="blur" />
          <feMerge>
            <feMergeNode in="blur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* The animated line */}
      <path
        d={pathD}
        fill="none"
        stroke={LINE_COLOR}
        strokeWidth={2.5}
        strokeLinecap="round"
        strokeLinejoin="round"
        strokeDasharray={totalLength}
        strokeDashoffset={dashOffset}
        filter="url(#lineGlow)"
      />

      {/* Data-point circles — appear as line reaches them */}
      {points.map((p, i) => {
        // Each point appears when the line reaches it
        const pointFraction = i / (points.length - 1);
        const pointOpacity = interpolate(
          drawProgress,
          [Math.max(0, pointFraction - 0.05), pointFraction + 0.05],
          [0, 1],
          { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
        );

        return (
          <g key={i}>
            <circle
              cx={p.x}
              cy={p.y}
              r={4}
              fill={LINE_COLOR}
              opacity={pointOpacity}
            />
            <circle
              cx={p.x}
              cy={p.y}
              r={7}
              fill="none"
              stroke={LINE_COLOR}
              strokeWidth={1.5}
              opacity={pointOpacity * 0.4}
            />
          </g>
        );
      })}
    </svg>
  );
};

export default AnimatedLine;
