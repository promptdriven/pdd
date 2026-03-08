import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { LAYOUT, COLORS, TYPOGRAPHY, PLATFORM_DATA } from './constants';

interface MetricRowProps {
  label: string;
  y: number;
  values: [number, number, number];
  unit: string;
  prefix?: string;
  colors: [string, string, string];
  duration: number;
  showProgressBar?: boolean;
}

export const MetricRow: React.FC<MetricRowProps> = ({
  label,
  y,
  values,
  unit,
  prefix = '',
  colors,
  duration,
  showProgressBar = false,
}) => {
  const frame = useCurrentFrame();

  // Count up animation with easeOutQuad
  const animatedValues = values.map((value) =>
    Math.round(
      interpolate(frame, [0, duration], [0, value], {
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
        easing: Easing.out(Easing.quad),
      })
    )
  );

  // Progress bar fill (only for monthly cost row)
  const maxValue = Math.max(...values);
  const barWidths = showProgressBar
    ? values.map((value, index) =>
        interpolate(
          frame,
          [0, duration],
          [0, (value / maxValue) * 400],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.inOut(Easing.cubic),
          }
        )
      )
    : [];

  const formatValue = (value: number, index: number) => {
    if (prefix === '$') {
      return `$${value.toLocaleString()}`;
    }
    return value.toLocaleString();
  };

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: y,
        width: CANVAS.width,
        height: LAYOUT.metricRow.height,
        display: 'flex',
        alignItems: 'center',
      }}
    >
      {/* Label */}
      <div
        style={{
          position: 'absolute',
          left: 110,
          fontFamily: TYPOGRAPHY.metricLabel.family,
          fontWeight: TYPOGRAPHY.metricLabel.weight,
          fontSize: TYPOGRAPHY.metricLabel.size,
          color: COLORS.label,
          width: 300,
        }}
      >
        {label}
      </div>

      {/* Values */}
      {LAYOUT.columnHeader.positions.map((x, index) => (
        <div
          key={index}
          style={{
            position: 'absolute',
            left: x,
            width: LAYOUT.columnHeader.width,
            display: 'flex',
            flexDirection: 'column',
            alignItems: 'center',
            gap: 10,
          }}
        >
          <div
            style={{
              fontFamily: TYPOGRAPHY.numberValue.family,
              fontWeight: TYPOGRAPHY.numberValue.weight,
              fontSize: TYPOGRAPHY.numberValue.size,
              color: colors[index],
            }}
          >
            {formatValue(animatedValues[index], index)}
            <span
              style={{
                fontSize: TYPOGRAPHY.metricLabel.size,
                marginLeft: 8,
                color: COLORS.label,
              }}
            >
              {unit}
            </span>
          </div>

          {/* Progress Bar */}
          {showProgressBar && (
            <div
              style={{
                width: 400,
                height: 12,
                backgroundColor: 'rgba(255,255,255,0.1)',
                borderRadius: 6,
                overflow: 'hidden',
              }}
            >
              <div
                style={{
                  width: barWidths[index],
                  height: '100%',
                  backgroundColor: colors[index],
                  transition: 'width 0.3s ease',
                }}
              />
            </div>
          )}
        </div>
      ))}
    </div>
  );
};

const CANVAS = { width: 1920, height: 1080 };
