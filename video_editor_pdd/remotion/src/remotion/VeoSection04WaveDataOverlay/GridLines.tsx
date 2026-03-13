import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, ANIMATION, CHART, type WaveOverlayLayout } from './constants';

export const GridLines: React.FC<{ layout: WaveOverlayLayout }> = ({ layout }) => {
  const frame = useCurrentFrame();

  // Grid lines draw from left to right (easeOutQuad), start at 5% for frame-0 visibility
  const drawProgress = interpolate(
    frame,
    [ANIMATION.gridDrawStart, ANIMATION.gridDrawEnd],
    [0.05, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const chartWidth = layout.chart.right - layout.chart.left;
  const chartHeight = layout.chart.bottom - layout.chart.top;

  return (
    <svg
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        width: layout.width,
        height: layout.height,
      }}
    >
      {CHART.gridYValues.map((yVal) => {
        // Map data y-value to pixel position
        const yNorm = (yVal - CHART.yMin) / (CHART.yMax - CHART.yMin);
        const yPx = layout.chart.bottom - yNorm * chartHeight;
        const lineWidth = chartWidth * drawProgress;

        return (
          <line
            key={yVal}
            x1={layout.chart.left}
            y1={yPx}
            x2={layout.chart.left + lineWidth}
            y2={yPx}
            stroke={COLORS.gridLine}
            strokeWidth={1}
          />
        );
      })}
    </svg>
  );
};
