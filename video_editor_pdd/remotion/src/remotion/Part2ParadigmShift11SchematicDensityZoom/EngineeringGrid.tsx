import React from 'react';
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  GRID_COLOR,
  GRID_OPACITY,
  GRID_SPACING,
} from './constants';

/**
 * Faint engineering-paper grid background.
 */
const EngineeringGrid: React.FC = () => {
  const lines: React.ReactNode[] = [];
  // Vertical lines
  for (let x = 0; x <= CANVAS_WIDTH; x += GRID_SPACING) {
    lines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={CANVAS_HEIGHT}
        stroke={GRID_COLOR}
        strokeWidth={1}
      />
    );
  }
  // Horizontal lines
  for (let y = 0; y <= CANVAS_HEIGHT; y += GRID_SPACING) {
    lines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={CANVAS_WIDTH}
        y2={y}
        stroke={GRID_COLOR}
        strokeWidth={1}
      />
    );
  }

  return (
    <svg
      width={CANVAS_WIDTH}
      height={CANVAS_HEIGHT}
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        opacity: GRID_OPACITY,
      }}
    >
      {lines}
    </svg>
  );
};

export default EngineeringGrid;
