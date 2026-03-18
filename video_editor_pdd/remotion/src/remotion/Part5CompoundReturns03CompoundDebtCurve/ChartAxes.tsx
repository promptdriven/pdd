import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CHART_LEFT,
  CHART_RIGHT,
  CHART_TOP,
  CHART_BOTTOM,
  AXIS_COLOR,
  AXIS_LABEL_COLOR,
  AXES_DURATION,
  X_LABELS,
  Y_LABELS,
} from './constants';

export const ChartAxes: React.FC = () => {
  const frame = useCurrentFrame();

  // Axes draw in over AXES_DURATION frames with easeOut(quad)
  const drawProgress = interpolate(frame, [0, AXES_DURATION], [0, 1], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const labelOpacity = interpolate(frame, [AXES_DURATION * 0.5, AXES_DURATION], [0, 0.4], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // X-axis: horizontal line at y=800
  const xAxisEndX = CHART_LEFT + (CHART_RIGHT - CHART_LEFT) * drawProgress;
  // Y-axis: vertical line at x=200
  const yAxisEndY = CHART_BOTTOM - (CHART_BOTTOM - CHART_TOP) * drawProgress;

  // X-axis label positions
  const xLabelPositions = X_LABELS.map((_, i) => {
    const t = (i + 0.5) / X_LABELS.length;
    return CHART_LEFT + t * (CHART_RIGHT - CHART_LEFT);
  });

  // Y-axis label positions
  const yLabelPositions = Y_LABELS.map((_, i) => {
    const t = (i + 0.5) / Y_LABELS.length;
    return CHART_BOTTOM - t * (CHART_BOTTOM - CHART_TOP);
  });

  return (
    <>
      <svg
        width={1920}
        height={1080}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        {/* X-axis */}
        <line
          x1={CHART_LEFT}
          y1={CHART_BOTTOM}
          x2={xAxisEndX}
          y2={CHART_BOTTOM}
          stroke={AXIS_COLOR}
          strokeWidth={2}
          opacity={0.5}
        />
        {/* Y-axis */}
        <line
          x1={CHART_LEFT}
          y1={CHART_BOTTOM}
          x2={CHART_LEFT}
          y2={yAxisEndY}
          stroke={AXIS_COLOR}
          strokeWidth={2}
          opacity={0.5}
        />
      </svg>

      {/* Axis title: Time */}
      <div
        style={{
          position: 'absolute',
          left: (CHART_LEFT + CHART_RIGHT) / 2,
          top: CHART_BOTTOM + 50,
          transform: 'translateX(-50%)',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          color: AXIS_LABEL_COLOR,
          opacity: labelOpacity,
          letterSpacing: '0.05em',
          textTransform: 'uppercase' as const,
        }}
      >
        Time
      </div>

      {/* Axis title: Cost */}
      <div
        style={{
          position: 'absolute',
          left: CHART_LEFT - 60,
          top: (CHART_TOP + CHART_BOTTOM) / 2,
          transform: 'translateY(-50%) rotate(-90deg)',
          fontFamily: 'Inter, sans-serif',
          fontSize: 14,
          color: AXIS_LABEL_COLOR,
          opacity: labelOpacity,
          letterSpacing: '0.05em',
          textTransform: 'uppercase' as const,
        }}
      >
        Cost
      </div>

      {/* X-axis labels */}
      {X_LABELS.map((label, i) => (
        <div
          key={`x-${i}`}
          style={{
            position: 'absolute',
            left: xLabelPositions[i],
            top: CHART_BOTTOM + 15,
            transform: 'translateX(-50%)',
            fontFamily: 'Inter, sans-serif',
            fontSize: 11,
            color: AXIS_LABEL_COLOR,
            opacity: labelOpacity,
          }}
        >
          {label}
        </div>
      ))}

      {/* Y-axis labels */}
      {Y_LABELS.map((label, i) => (
        <div
          key={`y-${i}`}
          style={{
            position: 'absolute',
            left: CHART_LEFT - 40,
            top: yLabelPositions[i],
            transform: 'translateY(-50%)',
            fontFamily: 'Inter, sans-serif',
            fontSize: 11,
            color: AXIS_LABEL_COLOR,
            opacity: labelOpacity,
            textAlign: 'right' as const,
            width: 30,
          }}
        >
          {label}
        </div>
      ))}
    </>
  );
};
