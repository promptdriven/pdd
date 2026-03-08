import React from 'react';
import { Easing, interpolate, useCurrentFrame } from 'remotion';
import { DIMENSIONS, CHART_DATA, TIMING, TYPOGRAPHY, MAX_VALUE } from './constants';

interface ValueLabelsProps {
  centerX: number;
  centerY: number;
}

export const ValueLabels: React.FC<ValueLabelsProps> = ({ centerX, centerY }) => {
  const frame = useCurrentFrame();

  const chartLeft = centerX - DIMENSIONS.chartWidth / 2;
  const chartBottom = centerY + DIMENSIONS.chartHeight / 2;

  const totalBarsWidth = CHART_DATA.length * DIMENSIONS.barWidth + (CHART_DATA.length - 1) * DIMENSIONS.barGap;
  const startX = chartLeft + (DIMENSIONS.chartWidth - totalBarsWidth) / 2;

  const opacity = interpolate(
    frame,
    [TIMING.labelsStart, TIMING.labelsStart + TIMING.labelsDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.5)),
    }
  );

  const scale = interpolate(
    frame,
    [TIMING.labelsStart, TIMING.labelsStart + TIMING.labelsDuration],
    [0.8, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.back(1.5)),
    }
  );

  return (
    <>
      {CHART_DATA.map((item, index) => {
        const barX = startX + index * (DIMENSIONS.barWidth + DIMENSIONS.barGap);
        const labelX = barX + DIMENSIONS.barWidth / 2;
        const barHeight = (item.value / MAX_VALUE) * DIMENSIONS.chartHeight;
        const labelY = chartBottom - barHeight - DIMENSIONS.valueLabelOffset;

        return (
          <text
            key={item.category}
            x={labelX}
            y={labelY}
            fill={item.color}
            fontSize={TYPOGRAPHY.valueLabelSize}
            fontFamily={TYPOGRAPHY.fontFamily}
            fontWeight="700"
            textAnchor="middle"
            dominantBaseline="baseline"
            opacity={opacity}
            style={{
              transform: `scale(${scale})`,
              transformOrigin: `${labelX}px ${labelY}px`,
            }}
          >
            {item.value}%
          </text>
        );
      })}
    </>
  );
};
