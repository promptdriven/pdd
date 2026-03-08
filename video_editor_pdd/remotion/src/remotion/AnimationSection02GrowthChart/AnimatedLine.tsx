import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { CHART_CONFIG, GROWTH_DATA, AXIS_CONFIG, ANIMATION_TIMING } from './constants';

export const AnimatedLine: React.FC = () => {
  const frame = useCurrentFrame();
  const { chartArea, colors, strokeWidths } = CHART_CONFIG;
  const { start, duration } = ANIMATION_TIMING.lineDrawIn;

  const chartX = chartArea.marginLeft;
  const chartY = chartArea.marginTop;
  const chartWidth = chartArea.width;
  const chartHeight = chartArea.height;

  const maxY = Math.max(...GROWTH_DATA.map(d => d.y));
  const minY = 0;

  // Convert data coordinates to screen coordinates
  const points = GROWTH_DATA.map((d, i) => ({
    x: chartX + (chartWidth / (GROWTH_DATA.length - 1)) * i,
    y: chartY + chartHeight - ((d.y - minY) / (maxY - minY)) * chartHeight,
  }));

  // Create path string
  const linePath = points.map((p, i) => `${i === 0 ? 'M' : 'L'} ${p.x} ${p.y}`).join(' ');

  // Create area path (same as line but closed to bottom)
  const areaPath = `${linePath} L ${points[points.length - 1].x} ${AXIS_CONFIG.xAxisY} L ${chartX} ${AXIS_CONFIG.xAxisY} Z`;

  const progress = interpolate(frame, [start, start + duration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.cubic),
  });

  // Calculate total path length for stroke-dasharray animation
  const strokeDashoffset = interpolate(progress, [0, 1], [1, 0]);

  return (
    <svg
      width={CHART_CONFIG.width}
      height={CHART_CONFIG.height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      <defs>
        <linearGradient id="areaGradient" x1="0" x2="0" y1="0" y2="1">
          <stop offset="0%" stopColor="rgba(59, 130, 246, 0.3)" />
          <stop offset="100%" stopColor="rgba(59, 130, 246, 0)" />
        </linearGradient>
        <filter id="glow">
          <feGaussianBlur stdDeviation="4" result="coloredBlur" />
          <feMerge>
            <feMergeNode in="coloredBlur" />
            <feMergeNode in="SourceGraphic" />
          </feMerge>
        </filter>
      </defs>

      {/* Area fill */}
      <path
        d={areaPath}
        fill="url(#areaGradient)"
        opacity={progress}
      />

      {/* Data line with glow */}
      <path
        d={linePath}
        fill="none"
        stroke={colors.dataLine}
        strokeWidth={strokeWidths.dataLine}
        strokeLinecap="round"
        strokeLinejoin="round"
        filter="url(#glow)"
        strokeDasharray="1"
        strokeDashoffset={strokeDashoffset}
        style={{
          pathLength: 1,
        }}
      />
    </svg>
  );
};
