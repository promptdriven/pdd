import React from 'react';
import { AbsoluteFill, interpolate, useCurrentFrame, Easing } from 'remotion';
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  GRID_CELL_SIZE,
  GRID_LINE_COLOR,
  PHASE_GRID_DIM_START,
  PHASE_GRID_DIM_END,
} from './constants';

/**
 * Renders a code-block-style grid background that dims from full to 30% opacity.
 */
export const BackgroundGrid: React.FC = () => {
  const frame = useCurrentFrame();

  const gridOpacity = interpolate(
    frame,
    [PHASE_GRID_DIM_START, PHASE_GRID_DIM_END],
    [0.6, 0.3],
    { extrapolateLeft: 'clamp', extrapolateRight: 'clamp' },
  );

  const cols = Math.ceil(CANVAS_WIDTH / GRID_CELL_SIZE);
  const rows = Math.ceil(CANVAS_HEIGHT / GRID_CELL_SIZE);

  const verticalLines: React.ReactNode[] = [];
  for (let i = 0; i <= cols; i++) {
    verticalLines.push(
      <line
        key={`v-${i}`}
        x1={i * GRID_CELL_SIZE}
        y1={0}
        x2={i * GRID_CELL_SIZE}
        y2={CANVAS_HEIGHT}
        stroke={GRID_LINE_COLOR}
        strokeWidth={1}
      />,
    );
  }

  const horizontalLines: React.ReactNode[] = [];
  for (let j = 0; j <= rows; j++) {
    horizontalLines.push(
      <line
        key={`h-${j}`}
        x1={0}
        y1={j * GRID_CELL_SIZE}
        x2={CANVAS_WIDTH}
        y2={j * GRID_CELL_SIZE}
        stroke={GRID_LINE_COLOR}
        strokeWidth={1}
      />,
    );
  }

  // Sprinkle a few "code block" rectangles for texture
  const codeBlocks = [
    { x: 3, y: 2, w: 6, h: 2 },
    { x: 12, y: 5, w: 8, h: 3 },
    { x: 25, y: 1, w: 10, h: 4 },
    { x: 5, y: 10, w: 7, h: 2 },
    { x: 18, y: 14, w: 9, h: 3 },
    { x: 35, y: 8, w: 12, h: 5 },
    { x: 50, y: 3, w: 6, h: 3 },
    { x: 8, y: 22, w: 10, h: 4 },
    { x: 40, y: 18, w: 8, h: 3 },
    { x: 28, y: 25, w: 14, h: 4 },
  ];

  return (
    <AbsoluteFill style={{ opacity: gridOpacity }}>
      <svg
        width={CANVAS_WIDTH}
        height={CANVAS_HEIGHT}
        viewBox={`0 0 ${CANVAS_WIDTH} ${CANVAS_HEIGHT}`}
        style={{ position: 'absolute', top: 0, left: 0 }}
      >
        {verticalLines}
        {horizontalLines}
        {codeBlocks.map((block, idx) => (
          <rect
            key={`cb-${idx}`}
            x={block.x * GRID_CELL_SIZE}
            y={block.y * GRID_CELL_SIZE}
            width={block.w * GRID_CELL_SIZE}
            height={block.h * GRID_CELL_SIZE}
            fill={GRID_LINE_COLOR}
            opacity={0.3}
            rx={4}
          />
        ))}
      </svg>
    </AbsoluteFill>
  );
};

export default BackgroundGrid;
