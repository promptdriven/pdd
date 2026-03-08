import React from 'react';
import { interpolate, useCurrentFrame } from 'remotion';
import { COLORS, DIMENSIONS, CHART_DATA, TIMING, TYPOGRAPHY } from './constants';

interface XAxisProps {
  centerX: number;
  centerY: number;
}

export const XAxis: React.FC<XAxisProps> = ({ centerX, centerY }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [TIMING.gridFadeStart, TIMING.gridFadeStart + TIMING.gridFadeDuration],
    [0, 1],
    { extrapolateRight: 'clamp' }
  );

  const chartLeft = centerX - DIMENSIONS.chartWidth / 2;
  const chartBottom = centerY + DIMENSIONS.chartHeight / 2;

  const totalBarsWidth = CHART_DATA.length * DIMENSIONS.barWidth + (CHART_DATA.length - 1) * DIMENSIONS.barGap;
  const startX = chartLeft + (DIMENSIONS.chartWidth - totalBarsWidth) / 2;

  return (
    <>
      {CHART_DATA.map((item, index) => {
        const barX = startX + index * (DIMENSIONS.barWidth + DIMENSIONS.barGap);
        const labelX = barX + DIMENSIONS.barWidth / 2;

        return (
          <text
            key={item.category}
            x={labelX}
            y={chartBottom + 40}
            fill={COLORS.categoryLabel}
            fontSize={TYPOGRAPHY.categoryLabelSize}
            fontFamily={TYPOGRAPHY.fontFamily}
            fontWeight="600"
            textAnchor="middle"
            opacity={opacity}
          >
            {item.category}
          </text>
        );
      })}
    </>
  );
};
