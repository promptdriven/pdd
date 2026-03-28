import React from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';

const GRID_LINE_COLOR = '#1E293B';
const GRID_LINE_OPACITY = 0.12;
const GRID_SPACING = 40;
const GRID_LABEL_COLOR = '#64748B';
const GRID_LABEL_OPACITY = 0.2;
const LABEL_FONT_SIZE = 10;

const GRID_ORIGIN_X = 80;
const GRID_ORIGIN_Y = 80;
const GRID_COLS = 20;
const GRID_ROWS = 10;

interface CoordinateGridProps {
  panelWidth: number;
  panelHeight: number;
  showLabels: boolean;
}

export const CoordinateGrid: React.FC<CoordinateGridProps> = ({
  panelWidth,
  panelHeight,
  showLabels,
}) => {
  const frame = useCurrentFrame();

  // Grid fades in over first 30 frames
  const gridOpacity = interpolate(frame, [0, 30], [0, 1], {
    easing: Easing.out(Easing.quad),
    extrapolateRight: 'clamp',
  });

  // Labels fade in starting at frame 150
  const labelOpacity = showLabels
    ? interpolate(frame, [150, 180], [0, GRID_LABEL_OPACITY], {
        easing: Easing.out(Easing.quad),
        extrapolateLeft: 'clamp',
        extrapolateRight: 'clamp',
      })
    : 0;

  const verticalLines: React.ReactNode[] = [];
  for (let col = 0; col <= GRID_COLS; col++) {
    const x = GRID_ORIGIN_X + col * GRID_SPACING;
    verticalLines.push(
      <line
        key={`v-${col}`}
        x1={x}
        y1={GRID_ORIGIN_Y}
        x2={x}
        y2={GRID_ORIGIN_Y + GRID_ROWS * GRID_SPACING}
        stroke={GRID_LINE_COLOR}
        strokeWidth={1}
        opacity={GRID_LINE_OPACITY * gridOpacity}
      />
    );
  }

  const horizontalLines: React.ReactNode[] = [];
  for (let row = 0; row <= GRID_ROWS; row++) {
    const y = GRID_ORIGIN_Y + row * GRID_SPACING;
    horizontalLines.push(
      <line
        key={`h-${row}`}
        x1={GRID_ORIGIN_X}
        y1={y}
        x2={GRID_ORIGIN_X + GRID_COLS * GRID_SPACING}
        y2={y}
        stroke={GRID_LINE_COLOR}
        strokeWidth={1}
        opacity={GRID_LINE_OPACITY * gridOpacity}
      />
    );
  }

  // Select labels at edges
  const labels: React.ReactNode[] = [];
  if (labelOpacity > 0) {
    for (let col = 0; col <= GRID_COLS; col += 5) {
      labels.push(
        <text
          key={`lx-${col}`}
          x={GRID_ORIGIN_X + col * GRID_SPACING}
          y={GRID_ORIGIN_Y + GRID_ROWS * GRID_SPACING + 16}
          fill={GRID_LABEL_COLOR}
          opacity={labelOpacity}
          fontSize={LABEL_FONT_SIZE}
          fontFamily="Inter, sans-serif"
          textAnchor="middle"
        >
          {col}
        </text>
      );
    }
    for (let row = 0; row <= GRID_ROWS; row += 5) {
      labels.push(
        <text
          key={`ly-${row}`}
          x={GRID_ORIGIN_X - 14}
          y={GRID_ORIGIN_Y + row * GRID_SPACING + 4}
          fill={GRID_LABEL_COLOR}
          opacity={labelOpacity}
          fontSize={LABEL_FONT_SIZE}
          fontFamily="Inter, sans-serif"
          textAnchor="end"
        >
          {row}
        </text>
      );
    }
  }

  return (
    <svg
      width={panelWidth}
      height={panelHeight}
      style={{ position: 'absolute', top: 0, left: 0 }}
    >
      {verticalLines}
      {horizontalLines}
      {labels}
    </svg>
  );
};

export default CoordinateGrid;
