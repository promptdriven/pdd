// CodeBlockGrid.tsx — Renders the growing code-block grid.
// Smoothly transitions between 4×4 → 8×8 → 16×16 → 32×32 grids.

import React, { useMemo } from 'react';
import { useCurrentFrame, interpolate, Easing } from 'remotion';
import {
  GROWTH_STAGES,
  TRANSITION_DURATION,
  BLOCK_FILL,
  BLOCK_BORDER,
  BLOCK_GAP,
  GRID_CENTER_X,
  GRID_CENTER_Y,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
} from './constants';

/**
 * Compute the current grid size and block dimensions for a given frame.
 */
function useGridState(frame: number) {
  // Find which stage we're in (or transitioning to)
  let currentStageIdx = 0;
  for (let i = GROWTH_STAGES.length - 1; i >= 0; i--) {
    if (frame >= GROWTH_STAGES[i].startFrame) {
      currentStageIdx = i;
      break;
    }
  }

  const currentStage = GROWTH_STAGES[currentStageIdx];
  const prevStage = currentStageIdx > 0 ? GROWTH_STAGES[currentStageIdx - 1] : null;

  // Compute transition progress
  const transitionStart = currentStage.startFrame;
  const transitionEnd = transitionStart + TRANSITION_DURATION;

  let progress = 1;
  if (frame < transitionEnd && currentStageIdx > 0) {
    progress = interpolate(frame, [transitionStart, transitionEnd], [0, 1], {
      easing: Easing.inOut(Easing.cubic),
      extrapolateLeft: 'clamp',
      extrapolateRight: 'clamp',
    });
  }

  const fromSize = prevStage ? prevStage.gridSize : currentStage.gridSize;
  const toSize = currentStage.gridSize;

  // Interpolated grid size for smooth visual
  const gridSize = Math.round(fromSize + (toSize - fromSize) * progress);

  // Compute block size so grid fits nicely on screen
  // Max grid extent: leave 200px margin on each side
  const maxExtent = Math.min(CANVAS_WIDTH, CANVAS_HEIGHT) - 200;
  const blockSize = Math.max(
    2,
    (maxExtent - BLOCK_GAP * (gridSize - 1)) / gridSize,
  );

  return { gridSize, blockSize, progress, currentStageIdx };
}

interface CodeBlockGridProps {
  /** Optional: provide the set of block flat-indices to render with overlays */
  children?: React.ReactNode;
}

export const CodeBlockGrid: React.FC<CodeBlockGridProps> = ({ children }) => {
  const frame = useCurrentFrame();
  const { gridSize, blockSize } = useGridState(frame);

  // Fade-in the initial grid — visible from frame 0, reaches full opacity at frame 30
  const gridOpacity = interpolate(frame, [0, 20], [0.4, 1], {
    extrapolateLeft: 'clamp',
    extrapolateRight: 'clamp',
  });

  const totalWidth = gridSize * blockSize + (gridSize - 1) * BLOCK_GAP;
  const totalHeight = gridSize * blockSize + (gridSize - 1) * BLOCK_GAP;

  const originX = GRID_CENTER_X - totalWidth / 2;
  const originY = GRID_CENTER_Y - totalHeight / 2;

  // Only render visible blocks (optimization for 32×32 = 1024 blocks)
  const blocks = useMemo(() => {
    const items: React.ReactNode[] = [];
    for (let row = 0; row < gridSize; row++) {
      for (let col = 0; col < gridSize; col++) {
        const x = col * (blockSize + BLOCK_GAP);
        const y = row * (blockSize + BLOCK_GAP);
        items.push(
          <rect
            key={`${row}-${col}`}
            x={x}
            y={y}
            width={blockSize}
            height={blockSize}
            fill={BLOCK_FILL}
            stroke={BLOCK_BORDER}
            strokeWidth={1}
            rx={blockSize > 10 ? 2 : 0}
          />,
        );
      }
    }
    return items;
  }, [gridSize, blockSize]);

  return (
    <div
      style={{
        position: 'absolute',
        left: 0,
        top: 0,
        width: '100%',
        height: '100%',
        opacity: gridOpacity,
      }}
    >
      <svg
        width={totalWidth}
        height={totalHeight}
        viewBox={`0 0 ${totalWidth} ${totalHeight}`}
        style={{
          position: 'absolute',
          left: originX,
          top: originY,
        }}
      >
        {blocks}
      </svg>
      {children}
    </div>
  );
};

export default CodeBlockGrid;

/**
 * Utility hook exported for other sub-components that need grid geometry.
 */
export function useGridGeometry() {
  const frame = useCurrentFrame();
  const { gridSize, blockSize } = useGridState(frame);

  const totalWidth = gridSize * blockSize + (gridSize - 1) * BLOCK_GAP;
  const totalHeight = gridSize * blockSize + (gridSize - 1) * BLOCK_GAP;

  const originX = GRID_CENTER_X - totalWidth / 2;
  const originY = GRID_CENTER_Y - totalHeight / 2;

  return { gridSize, blockSize, totalWidth, totalHeight, originX, originY };
}
