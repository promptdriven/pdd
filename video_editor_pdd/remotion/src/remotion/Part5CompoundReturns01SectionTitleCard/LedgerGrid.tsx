import React from 'react';
import {
  WIDTH,
  HEIGHT,
  GRID_H_SPACING,
  GRID_V_ACCENT_EVERY,
  GRID_COLOR,
  GRID_H_OPACITY,
  GRID_V_OPACITY,
} from './constants';

/**
 * Faint ledger-paper grid — horizontal lines at 40px spacing
 * with slightly brighter vertical accents every 120px.
 */
export const LedgerGrid: React.FC<{ opacity: number }> = ({ opacity }) => {
  const hLines: React.ReactNode[] = [];
  const vLines: React.ReactNode[] = [];

  for (let y = GRID_H_SPACING; y < HEIGHT; y += GRID_H_SPACING) {
    hLines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={WIDTH}
        y2={y}
        stroke={GRID_COLOR}
        strokeOpacity={GRID_H_OPACITY}
        strokeWidth={1}
      />,
    );
  }

  for (let x = GRID_V_ACCENT_EVERY; x < WIDTH; x += GRID_V_ACCENT_EVERY) {
    vLines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={HEIGHT}
        stroke={GRID_COLOR}
        strokeOpacity={GRID_V_OPACITY}
        strokeWidth={1}
      />,
    );
  }

  return (
    <svg
      width={WIDTH}
      height={HEIGHT}
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        opacity,
      }}
    >
      {hLines}
      {vLines}
    </svg>
  );
};
