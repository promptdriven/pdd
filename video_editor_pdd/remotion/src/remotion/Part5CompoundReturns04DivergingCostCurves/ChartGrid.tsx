import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  WIDTH,
  HEIGHT,
  GRID_COLOR,
  AXES_START,
  AXES_DURATION,
} from './constants';

/**
 * Subtle background grid lines that fade in with axes.
 * Horizontal lines at 80px intervals, vertical lines at year marker positions.
 */
export const ChartGrid: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(
    frame,
    [AXES_START, AXES_START + AXES_DURATION],
    [0.015, 0.05],
    { extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  const horizontalYs: number[] = [];
  for (let y = 100; y <= 820; y += 80) {
    horizontalYs.push(y);
  }

  const verticalXs = [180, 484, 788, 1092, 1396, 1700];

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {horizontalYs.map((y) => (
        <line
          key={`h-${y}`}
          x1={180}
          y1={y}
          x2={1700}
          y2={y}
          stroke={GRID_COLOR}
          strokeWidth={1}
          opacity={opacity}
        />
      ))}
      {verticalXs.map((x) => (
        <line
          key={`v-${x}`}
          x1={x}
          y1={100}
          x2={x}
          y2={820}
          stroke={GRID_COLOR}
          strokeWidth={1}
          opacity={opacity}
        />
      ))}
    </svg>
  );
};
