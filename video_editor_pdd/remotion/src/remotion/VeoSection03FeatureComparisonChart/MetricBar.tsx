import React from 'react';
import { useCurrentFrame } from 'remotion';
import { interpolate, Easing } from 'remotion';
import {
  CHART_DIMENSIONS,
  TYPOGRAPHY,
  ANIMATION_TIMING,
  METRIC_COLORS,
} from './constants';

interface MetricBarProps {
  metric: 'Quality' | 'Speed' | 'Cost' | 'Control';
  value: number;
  yBase: number;
  metricIndex: number;
  delay: number;
}

export const MetricBar: React.FC<MetricBarProps> = ({
  metric,
  value,
  yBase,
  metricIndex,
  delay,
}) => {
  const frame = useCurrentFrame();

  // Calculate bar width progress (0 to 1)
  const progress = interpolate(
    frame,
    [delay, delay + ANIMATION_TIMING.BAR_GROWTH_DURATION],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.bezier(0.22, 1, 0.36, 1), // easeOutCubic
    }
  );

  // Bar width based on value (out of 10) and progress
  const maxBarWidth = CHART_DIMENSIONS.CHART_WIDTH;
  const barWidth = (value / 10) * maxBarWidth * progress;

  // Position calculation
  const yPosition = yBase + metricIndex * CHART_DIMENSIONS.METRIC_SPACING;

  // Value label opacity (fade in when bar is mostly grown)
  const labelOpacity = interpolate(frame, [delay + 20, delay + 30], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  // Pulse effect for VEO 2 bars during hold phase
  const isPulsePhase = frame >= ANIMATION_TIMING.HOLD_START;
  const pulseScale = isPulsePhase
    ? interpolate(
        Math.sin((frame - ANIMATION_TIMING.HOLD_START) * 0.1),
        [-1, 1],
        [0.98, 1.0],
        {
          easing: Easing.inOut(Easing.sin),
        }
      )
    : 1.0;

  const color = METRIC_COLORS[metric];

  return (
    <>
      {/* Metric label on the left */}
      <div
        style={{
          position: 'absolute',
          left: CHART_DIMENSIONS.LABEL_X + 200,
          top: yPosition + 10,
          fontFamily: TYPOGRAPHY.METRIC_LABEL.FONT_FAMILY,
          fontWeight: TYPOGRAPHY.METRIC_LABEL.FONT_WEIGHT,
          fontSize: TYPOGRAPHY.METRIC_LABEL.FONT_SIZE,
          color: TYPOGRAPHY.METRIC_LABEL.COLOR,
          opacity: progress,
        }}
      >
        {metric}
      </div>

      {/* The bar itself */}
      <div
        style={{
          position: 'absolute',
          left: CHART_DIMENSIONS.CHART_START_X,
          top: yPosition,
          width: barWidth,
          height: CHART_DIMENSIONS.BAR_HEIGHT,
          backgroundColor: color,
          borderRadius: CHART_DIMENSIONS.BAR_CORNER_RADIUS,
          transform: `scaleY(${pulseScale})`,
          transformOrigin: 'left center',
        }}
      />

      {/* Value label on the right */}
      <div
        style={{
          position: 'absolute',
          left: CHART_DIMENSIONS.CHART_START_X + barWidth + 10,
          top: yPosition + 10,
          fontFamily: TYPOGRAPHY.VALUE_LABEL.FONT_FAMILY,
          fontWeight: TYPOGRAPHY.VALUE_LABEL.FONT_WEIGHT,
          fontSize: TYPOGRAPHY.VALUE_LABEL.FONT_SIZE,
          color: TYPOGRAPHY.VALUE_LABEL.COLOR,
          opacity: labelOpacity,
        }}
      >
        {value.toFixed(1)}/10
      </div>
    </>
  );
};
