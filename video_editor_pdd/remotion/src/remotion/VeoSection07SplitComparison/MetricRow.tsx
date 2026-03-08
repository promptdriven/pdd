import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  CANVAS,
  COLORS,
  POSITIONS,
  DIMENSIONS,
  TYPOGRAPHY,
  ANIMATION,
} from './constants';

interface MetricRowProps {
  label: string;
  oceanValue: string;
  forestValue: string;
  oceanPercent: number;
  forestPercent: number;
  index: number;
}

export const MetricRow: React.FC<MetricRowProps> = ({
  label,
  oceanValue,
  forestValue,
  oceanPercent,
  forestPercent,
  index,
}) => {
  const frame = useCurrentFrame();
  const rowStart = ANIMATION.metricsStart + index * ANIMATION.metricsStaggerDelay;

  const opacity = interpolate(
    frame,
    [rowStart, rowStart + 12],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const translateY = interpolate(
    frame,
    [rowStart, rowStart + 12],
    [10, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.cubic),
    },
  );

  const barProgress = interpolate(
    frame,
    [rowStart + 4, rowStart + ANIMATION.metricsDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.quad),
    },
  );

  const rowY = POSITIONS.metricsStartY + index * 70;
  const barY = rowY + 30;
  const halfWidth = CANVAS.width / 2;

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: CANVAS.width,
        height: CANVAS.height,
        opacity,
        transform: `translateY(${translateY}px)`,
      }}
    >
      {/* Label centered */}
      <div
        style={{
          position: 'absolute',
          left: halfWidth - 60,
          top: rowY,
          width: 120,
          textAlign: 'center',
        }}
      >
        <span
          style={{
            color: COLORS.metricText,
            fontFamily: TYPOGRAPHY.metric.fontFamily,
            fontWeight: TYPOGRAPHY.metric.fontWeight,
            fontSize: TYPOGRAPHY.metric.fontSize,
            textTransform: 'uppercase' as const,
            letterSpacing: '1.5px',
          }}
        >
          {label}
        </span>
      </div>

      {/* Ocean bar (extends left from center) */}
      <div
        style={{
          position: 'absolute',
          right: halfWidth + 70,
          top: barY,
          width: DIMENSIONS.metricBarWidth,
          height: DIMENSIONS.metricBarHeight,
          backgroundColor: COLORS.metricBarBg,
          borderRadius: 3,
          overflow: 'hidden',
          display: 'flex',
          justifyContent: 'flex-end',
        }}
      >
        <div
          style={{
            width: `${oceanPercent * barProgress}%`,
            height: '100%',
            backgroundColor: COLORS.metricBarOcean,
            borderRadius: 3,
          }}
        />
      </div>

      {/* Ocean value */}
      <div
        style={{
          position: 'absolute',
          right: halfWidth + 70 + DIMENSIONS.metricBarWidth + 12,
          top: barY - 5,
          textAlign: 'right',
        }}
      >
        <span
          style={{
            color: COLORS.oceanLabel,
            fontFamily: TYPOGRAPHY.metricValue.fontFamily,
            fontWeight: TYPOGRAPHY.metricValue.fontWeight,
            fontSize: TYPOGRAPHY.metricValue.fontSize,
          }}
        >
          {oceanValue}
        </span>
      </div>

      {/* Forest bar (extends right from center) */}
      <div
        style={{
          position: 'absolute',
          left: halfWidth + 70,
          top: barY,
          width: DIMENSIONS.metricBarWidth,
          height: DIMENSIONS.metricBarHeight,
          backgroundColor: COLORS.metricBarBg,
          borderRadius: 3,
          overflow: 'hidden',
        }}
      >
        <div
          style={{
            width: `${forestPercent * barProgress}%`,
            height: '100%',
            backgroundColor: COLORS.metricBarForest,
            borderRadius: 3,
          }}
        />
      </div>

      {/* Forest value */}
      <div
        style={{
          position: 'absolute',
          left: halfWidth + 70 + DIMENSIONS.metricBarWidth + 12,
          top: barY - 5,
        }}
      >
        <span
          style={{
            color: COLORS.forestLabel,
            fontFamily: TYPOGRAPHY.metricValue.fontFamily,
            fontWeight: TYPOGRAPHY.metricValue.fontWeight,
            fontSize: TYPOGRAPHY.metricValue.fontSize,
          }}
        >
          {forestValue}
        </span>
      </div>
    </div>
  );
};
