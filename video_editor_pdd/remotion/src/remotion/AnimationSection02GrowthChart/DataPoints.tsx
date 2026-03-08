import React from 'react';
import { interpolate, useCurrentFrame, Easing, spring } from 'remotion';
import { CHART_CONFIG, GROWTH_DATA, ANIMATION_TIMING } from './constants';

export const DataPoints: React.FC = () => {
  const frame = useCurrentFrame();
  const { chartArea, colors, strokeWidths, dataPointRadius } = CHART_CONFIG;
  const { start, duration } = ANIMATION_TIMING.pointsAppear;

  const chartX = chartArea.marginLeft;
  const chartY = chartArea.marginTop;
  const chartWidth = chartArea.width;
  const chartHeight = chartArea.height;

  const maxY = Math.max(...GROWTH_DATA.map(d => d.y));
  const minY = 0;

  const staggerDelay = duration / GROWTH_DATA.length;

  const points = GROWTH_DATA.map((d, i) => {
    const x = chartX + (chartWidth / (GROWTH_DATA.length - 1)) * i;
    const y = chartY + chartHeight - ((d.y - minY) / (maxY - minY)) * chartHeight;

    const pointStart = start + i * staggerDelay;

    // Use spring for elastic bounce effect
    const scale = spring({
      frame: frame - pointStart,
      fps: 30,
      config: {
        damping: 10,
        stiffness: 100,
        mass: 0.5,
      },
    });

    const opacity = interpolate(
      frame,
      [pointStart, pointStart + 10],
      [0, 1],
      {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      }
    );

    return (
      <g key={i} opacity={opacity}>
        <circle
          cx={x}
          cy={y}
          r={dataPointRadius * scale}
          fill={colors.dataPoint}
          stroke={colors.dataPointStroke}
          strokeWidth={strokeWidths.dataPoint}
        />
      </g>
    );
  });

  return (
    <svg
      width={CHART_CONFIG.width}
      height={CHART_CONFIG.height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {points}
    </svg>
  );
};
