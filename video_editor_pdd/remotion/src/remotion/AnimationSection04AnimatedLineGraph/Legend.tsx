import React from 'react';
import { interpolate, useCurrentFrame } from 'remotion';
import { COLORS, TYPOGRAPHY } from './constants';

interface LegendProps {
  startFrame: number;
  fadeInDuration: number;
}

export const Legend: React.FC<LegendProps> = ({ startFrame, fadeInDuration }) => {
  const frame = useCurrentFrame();
  const opacity = interpolate(
    frame,
    [startFrame, startFrame + fadeInDuration],
    [0, 1],
    {
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    }
  );

  const items = [
    { label: 'Target', color: COLORS.series1 },
    { label: 'Actual', color: COLORS.series2 },
  ];

  return (
    <div
      style={{
        position: 'absolute',
        top: 220,
        left: 1520,
        opacity,
        display: 'flex',
        flexDirection: 'column',
        gap: 16,
      }}
    >
      {items.map((item) => (
        <div
          key={item.label}
          style={{
            display: 'flex',
            alignItems: 'center',
            gap: 8,
          }}
        >
          <div
            style={{
              width: 12,
              height: 12,
              borderRadius: '50%',
              backgroundColor: item.color,
            }}
          />
          <div
            style={{
              fontFamily: TYPOGRAPHY.legend.fontFamily,
              fontWeight: TYPOGRAPHY.legend.fontWeight,
              fontSize: TYPOGRAPHY.legend.fontSize,
              color: COLORS.legendText,
            }}
          >
            {item.label}
          </div>
        </div>
      ))}
    </div>
  );
};
