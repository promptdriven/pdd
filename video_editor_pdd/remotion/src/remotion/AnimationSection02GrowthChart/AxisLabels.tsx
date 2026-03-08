import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { CHART_CONFIG, AXIS_CONFIG, ANIMATION_TIMING } from './constants';

export const AxisLabels: React.FC = () => {
  const frame = useCurrentFrame();
  const { chartArea, typography } = CHART_CONFIG;
  const { start, duration } = ANIMATION_TIMING.labelsFadeIn;

  const opacity = interpolate(frame, [start, start + duration], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.ease),
  });

  const scale = interpolate(frame, [start, start + duration], [0.8, 1.0], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.ease),
  });

  const chartX = chartArea.marginLeft;
  const chartWidth = chartArea.width;
  const chartY = chartArea.marginTop;
  const chartHeight = chartArea.height;

  // X-axis labels (Q1-Q4)
  const xLabels = AXIS_CONFIG.xLabels.map((label, i) => {
    const x = chartX + (chartWidth / (AXIS_CONFIG.xLabels.length - 1)) * i;
    const y = AXIS_CONFIG.xAxisY + 40;

    return (
      <div
        key={`x-${i}`}
        style={{
          position: 'absolute',
          left: x,
          top: y,
          transform: `translate(-50%, 0) scale(${scale})`,
          fontFamily: typography.axisLabel.fontFamily,
          fontWeight: typography.axisLabel.fontWeight,
          fontSize: typography.axisLabel.fontSize,
          color: typography.axisLabel.color,
          opacity,
        }}
      >
        {label}
      </div>
    );
  });

  // Y-axis labels (0K-200K)
  const yLabels = AXIS_CONFIG.yLabels.map((label, i) => {
    const x = AXIS_CONFIG.yAxisX - 60;
    const y = AXIS_CONFIG.xAxisY - (chartHeight / (AXIS_CONFIG.yLabels.length - 1)) * i;

    return (
      <div
        key={`y-${i}`}
        style={{
          position: 'absolute',
          left: x,
          top: y,
          transform: `translate(0, -50%) scale(${scale})`,
          fontFamily: typography.axisLabel.fontFamily,
          fontWeight: typography.axisLabel.fontWeight,
          fontSize: typography.axisLabel.fontSize,
          color: typography.axisLabel.color,
          opacity,
          textAlign: 'right',
        }}
      >
        {label}
      </div>
    );
  });

  return (
    <div style={{ position: 'absolute', top: 0, left: 0, width: '100%', height: '100%' }}>
      {xLabels}
      {yLabels}
    </div>
  );
};
