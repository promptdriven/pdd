import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import { COLORS, TYPOGRAPHY, ANIMATION } from './constants';

interface MetricCardProps {
  label: string;
  value: number;
  unit: string;
  suffix: string;
  index: number;
}

export const MetricCard: React.FC<MetricCardProps> = ({
  label,
  value,
  unit,
  suffix,
  index,
}) => {
  const frame = useCurrentFrame();

  const startFrame = ANIMATION.metricsStart + index * ANIMATION.metricsStagger;
  const endFrame = startFrame + ANIMATION.metricCountDuration;

  // Fade in
  const opacity = interpolate(
    frame,
    [startFrame, startFrame + 10],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  // Slide up
  const translateY = interpolate(
    frame,
    [startFrame, startFrame + 10],
    [20, 0],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(3)),
    },
  );

  // Counter animation
  const displayValue = Math.round(
    interpolate(frame, [startFrame, endFrame], [0, value], {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
      easing: Easing.out(Easing.poly(2)),
    }),
  );

  // Accent color cycles per metric
  const accentColors = [
    COLORS.accentBlue,
    COLORS.accentCyan,
    COLORS.accentGreen,
    COLORS.accentAmber,
  ];
  const accent = accentColors[index % accentColors.length];

  return (
    <div
      style={{
        opacity,
        transform: `translateY(${translateY}px)`,
        display: 'flex',
        flexDirection: 'column',
        alignItems: 'center',
        gap: 8,
        width: 160,
      }}
    >
      {/* Label */}
      <span
        style={{
          color: COLORS.metricLabel,
          fontSize: TYPOGRAPHY.metricLabel.fontSize,
          fontFamily: TYPOGRAPHY.metricLabel.fontFamily,
          fontWeight: TYPOGRAPHY.metricLabel.fontWeight,
          letterSpacing: TYPOGRAPHY.metricLabel.letterSpacing,
          textTransform: TYPOGRAPHY.metricLabel.textTransform,
          whiteSpace: 'nowrap',
        }}
      >
        {label}
      </span>

      {/* Value */}
      <div style={{ display: 'flex', alignItems: 'baseline', gap: 2 }}>
        <span
          style={{
            color: accent,
            fontSize: TYPOGRAPHY.metricValue.fontSize,
            fontFamily: TYPOGRAPHY.metricValue.fontFamily,
            fontWeight: TYPOGRAPHY.metricValue.fontWeight,
            letterSpacing: TYPOGRAPHY.metricValue.letterSpacing,
          }}
        >
          {displayValue}
        </span>
        <span
          style={{
            color: COLORS.metricValue,
            fontSize: TYPOGRAPHY.metricUnit.fontSize,
            fontFamily: TYPOGRAPHY.metricUnit.fontFamily,
            fontWeight: TYPOGRAPHY.metricUnit.fontWeight,
          }}
        >
          {unit}
        </span>
        {suffix && (
          <span
            style={{
              color: COLORS.labelText,
              fontSize: 12,
              fontFamily: 'Inter, sans-serif',
              fontWeight: 400,
              marginLeft: 2,
            }}
          >
            {suffix}
          </span>
        )}
      </div>

      {/* Underline accent */}
      <div
        style={{
          width: interpolate(
            frame,
            [startFrame + 5, startFrame + 15],
            [0, 40],
            { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
          ),
          height: 2,
          borderRadius: 1,
          backgroundColor: accent,
          opacity: 0.6,
        }}
      />
    </div>
  );
};
