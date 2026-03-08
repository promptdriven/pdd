import React from 'react';
import { AbsoluteFill } from 'remotion';
import { COLORS, GRID, SHAPES } from './constants';
import { BouncingShape } from './BouncingShape';

export const AnimationSection05AnimationShowcase: React.FC = () => {
  // Calculate grid positioning to center on canvas
  const totalGridWidth =
    GRID.cols * GRID.cellSize + (GRID.cols - 1) * GRID.gap;
  const totalGridHeight =
    GRID.rows * GRID.cellSize + (GRID.rows - 1) * GRID.gap;

  return (
    <AbsoluteFill
      style={{
        backgroundColor: COLORS.background,
      }}
    >
      {/* Grid container — centered */}
      <div
        style={{
          position: 'absolute',
          top: '50%',
          left: '50%',
          transform: 'translate(-50%, -50%)',
          width: totalGridWidth,
          height: totalGridHeight,
          display: 'grid',
          gridTemplateColumns: `repeat(${GRID.cols}, ${GRID.cellSize}px)`,
          gridTemplateRows: `repeat(${GRID.rows}, ${GRID.cellSize}px)`,
          gap: GRID.gap,
        }}
      >
        {SHAPES.map((shape, i) => (
          <BouncingShape
            key={i}
            type={shape.type}
            color={shape.color}
            size={shape.size}
            index={i}
          />
        ))}
      </div>
    </AbsoluteFill>
  );
};

export const defaultAnimationSection05AnimationShowcaseProps = {};

export default AnimationSection05AnimationShowcase;
