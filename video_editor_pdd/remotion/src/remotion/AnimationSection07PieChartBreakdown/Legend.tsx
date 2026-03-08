import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import { LEGEND } from './constants';

interface LegendItem {
  label: string;
  percentage: number;
  color: string;
}

interface LegendProps {
  items: readonly LegendItem[];
}

export const Legend: React.FC<LegendProps> = ({ items }) => {
  const frame = useCurrentFrame();

  return (
    <div
      style={{
        position: 'absolute',
        left: LEGEND.POSITION_X,
        top: LEGEND.POSITION_Y,
        display: 'flex',
        flexDirection: 'column',
        gap: '20px',
      }}
    >
      {items.map((item, index) => {
        // Stagger appearance with easeOutQuad
        const appearProgress = interpolate(
          frame,
          [index * 5, index * 5 + 10],
          [0, 1],
          {
            extrapolateLeft: 'clamp',
            extrapolateRight: 'clamp',
            easing: Easing.out(Easing.quad),
          }
        );

        return (
          <div
            key={item.label}
            style={{
              display: 'flex',
              alignItems: 'center',
              gap: '16px',
              opacity: appearProgress,
              transform: `translateX(${(1 - appearProgress) * 30}px)`,
            }}
          >
            {/* Color indicator circle */}
            <div
              style={{
                width: LEGEND.CIRCLE_SIZE,
                height: LEGEND.CIRCLE_SIZE,
                borderRadius: '50%',
                backgroundColor: item.color,
                flexShrink: 0,
              }}
            />

            {/* Label text */}
            <span
              style={{
                fontFamily: 'Inter, sans-serif',
                fontSize: LEGEND.LABEL_FONT_SIZE,
                fontWeight: 500,
                color: LEGEND.LABEL_COLOR,
                minWidth: '120px',
              }}
            >
              {item.label}
            </span>

            {/* Percentage */}
            <span
              style={{
                fontFamily: 'Inter, sans-serif',
                fontSize: LEGEND.LABEL_FONT_SIZE,
                fontWeight: 700,
                color: item.color,
              }}
            >
              {item.percentage}%
            </span>
          </div>
        );
      })}
    </div>
  );
};
