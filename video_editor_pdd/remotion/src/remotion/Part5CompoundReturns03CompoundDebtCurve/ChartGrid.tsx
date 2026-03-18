import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  WIDTH,
  HEIGHT,
  GRID_COLOR,
  GRID_OPACITY,
  H_GRID_SPACING,
  V_GRID_SPACING,
  GRID_FADE_DURATION,
} from './constants';

export const ChartGrid: React.FC = () => {
  const frame = useCurrentFrame();

  const opacity = interpolate(frame, [0, GRID_FADE_DURATION], [0, GRID_OPACITY], {
    extrapolateRight: 'clamp',
    easing: Easing.out(Easing.quad),
  });

  const horizontalLines: number[] = [];
  for (let y = H_GRID_SPACING; y < HEIGHT; y += H_GRID_SPACING) {
    horizontalLines.push(y);
  }

  const verticalLines: number[] = [];
  for (let x = V_GRID_SPACING; x < WIDTH; x += V_GRID_SPACING) {
    verticalLines.push(x);
  }

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {horizontalLines.map((y) => (
        <line
          key={`h-${y}`}
          x1={0}
          y1={y}
          x2={WIDTH}
          y2={y}
          stroke={GRID_COLOR}
          strokeWidth={1}
          opacity={opacity}
        />
      ))}
      {verticalLines.map((x) => (
        <line
          key={`v-${x}`}
          x1={x}
          y1={0}
          x2={x}
          y2={HEIGHT}
          stroke={GRID_COLOR}
          strokeWidth={1}
          opacity={opacity}
        />
      ))}
    </svg>
  );
};
