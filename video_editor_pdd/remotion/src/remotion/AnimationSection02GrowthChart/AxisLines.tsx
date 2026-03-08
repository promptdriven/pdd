import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { CHART_CONFIG, AXIS_CONFIG, ANIMATION_TIMING } from './constants';

export const AxisLines: React.FC = () => {
  const frame = useCurrentFrame();
  const { chartArea, colors, strokeWidths } = CHART_CONFIG;
  const { start, duration } = ANIMATION_TIMING.axisDrawIn;

  const chartX = chartArea.marginLeft;
  const chartWidth = chartArea.width;

  const progress = interpolate(frame, [start, start + duration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.inOut(Easing.quad),
  });

  const xAxisWidth = chartWidth * progress;
  const yAxisHeight = chartArea.height * progress;

  return (
    <svg
      width={CHART_CONFIG.width}
      height={CHART_CONFIG.height}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {/* X-axis */}
      <line
        x1={AXIS_CONFIG.yAxisX}
        y1={AXIS_CONFIG.xAxisY}
        x2={AXIS_CONFIG.yAxisX + xAxisWidth}
        y2={AXIS_CONFIG.xAxisY}
        stroke={colors.axisLine}
        strokeWidth={strokeWidths.axisLine}
      />

      {/* Y-axis */}
      <line
        x1={AXIS_CONFIG.yAxisX}
        y1={AXIS_CONFIG.xAxisY}
        x2={AXIS_CONFIG.yAxisX}
        y2={AXIS_CONFIG.xAxisY - yAxisHeight}
        stroke={colors.axisLine}
        strokeWidth={strokeWidths.axisLine}
      />
    </svg>
  );
};
