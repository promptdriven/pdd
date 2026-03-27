import React from 'react';
import { useCurrentFrame, interpolate } from 'remotion';
import { LEGEND_ITEMS } from './constants';

interface LegendProps {
  appearFrame: number;
}

export const Legend: React.FC<LegendProps> = ({ appearFrame }) => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [appearFrame, appearFrame + 30], [0, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  if (opacity <= 0) return null;

  return (
    <div
      style={{
        position: 'absolute',
        top: 960,
        left: 140,
        display: 'flex',
        gap: 40,
        opacity,
      }}
    >
      {LEGEND_ITEMS.map((item) => (
        <div
          key={item.label}
          style={{
            display: 'flex',
            alignItems: 'center',
            gap: 8,
          }}
        >
          <svg width={32} height={4}>
            <line
              x1={0}
              y1={2}
              x2={32}
              y2={2}
              stroke={item.color}
              strokeWidth={3}
              strokeDasharray={item.dashed ? '8 6' : 'none'}
            />
          </svg>
          <span
            style={{
              fontFamily: 'Inter, sans-serif',
              fontSize: 14,
              fontWeight: 600,
              color: item.color,
            }}
          >
            {item.label}
          </span>
        </div>
      ))}
    </div>
  );
};

export default Legend;
