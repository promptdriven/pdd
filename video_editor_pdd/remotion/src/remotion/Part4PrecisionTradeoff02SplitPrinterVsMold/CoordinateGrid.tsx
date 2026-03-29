import React from 'react';
import { interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  PANEL_WIDTH,
  CANVAS_HEIGHT,
  GRID_SPACING,
  GRID_LINE_COLOR,
  GRID_LINE_OPACITY,
  GRID_LABEL_COLOR,
  GRID_LABEL_OPACITY,
  GRID_LABEL_SIZE,
  GRID_ORIGIN_X,
  GRID_ORIGIN_Y,
  GRID_COLS,
  GRID_ROWS,
  HEADER_FONT_FAMILY,
  PHASE_ANIMATE_MID,
} from './constants';

interface CoordinateGridProps {
  panelOpacity: number;
}

export const CoordinateGrid: React.FC<CoordinateGridProps> = ({ panelOpacity }) => {
  const frame = useCurrentFrame();

  // Grid labels fade in at frame 150 over 30 frames
  const labelOpacity = interpolate(
    frame,
    [PHASE_ANIMATE_MID, PHASE_ANIMATE_MID + 30],
    [0, GRID_LABEL_OPACITY],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp', easing: Easing.out(Easing.quad) }
  );

  // Generate vertical grid lines
  const verticalLines: React.ReactNode[] = [];
  const numVertical = Math.floor(PANEL_WIDTH / GRID_SPACING);
  for (let i = 0; i <= numVertical; i++) {
    const x = i * GRID_SPACING;
    verticalLines.push(
      <line
        key={`v-${i}`}
        x1={x}
        y1={0}
        x2={x}
        y2={CANVAS_HEIGHT}
        stroke={GRID_LINE_COLOR}
        strokeOpacity={GRID_LINE_OPACITY}
        strokeWidth={1}
      />
    );
  }

  // Generate horizontal grid lines
  const horizontalLines: React.ReactNode[] = [];
  const numHorizontal = Math.floor(CANVAS_HEIGHT / GRID_SPACING);
  for (let i = 0; i <= numHorizontal; i++) {
    const y = i * GRID_SPACING;
    horizontalLines.push(
      <line
        key={`h-${i}`}
        x1={0}
        y1={y}
        x2={PANEL_WIDTH}
        y2={y}
        stroke={GRID_LINE_COLOR}
        strokeOpacity={GRID_LINE_OPACITY}
        strokeWidth={1}
      />
    );
  }

  // Grid coordinate labels at select intersections (every 4th intersection)
  const labels: React.ReactNode[] = [];
  for (let row = 0; row < GRID_ROWS; row += 4) {
    for (let col = 0; col < GRID_COLS; col += 4) {
      const x = GRID_ORIGIN_X + col * GRID_SPACING;
      const y = GRID_ORIGIN_Y + row * GRID_SPACING;
      labels.push(
        <text
          key={`label-${row}-${col}`}
          x={x + 4}
          y={y - 4}
          fill={GRID_LABEL_COLOR}
          fillOpacity={labelOpacity}
          fontSize={GRID_LABEL_SIZE}
          fontFamily={HEADER_FONT_FAMILY}
        >
          {col},{row}
        </text>
      );
    }
  }

  return (
    <svg
      width={PANEL_WIDTH}
      height={CANVAS_HEIGHT}
      style={{
        position: 'absolute',
        top: 0,
        left: 0,
        opacity: panelOpacity,
      }}
    >
      {verticalLines}
      {horizontalLines}
      {labels}
    </svg>
  );
};

export default CoordinateGrid;
