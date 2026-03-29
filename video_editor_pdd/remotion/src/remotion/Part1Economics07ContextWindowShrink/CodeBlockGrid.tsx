import React, { useMemo } from "react";
import { useCurrentFrame, interpolate } from "remotion";
import {
  BLOCK_FILL,
  BLOCK_BORDER,
  BLOCK_GAP,
  GRID_CENTER_X,
  GRID_CENTER_Y,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
} from "./constants";

/**
 * Computes the current effective grid size (fractional during transitions)
 * and renders a grid of code blocks that grows through the defined stages.
 */

const MAX_GRID_AREA = Math.min(CANVAS_WIDTH - 200, CANVAS_HEIGHT - 160);

function getBlockSize(gridSize: number): number {
  return Math.max(2, (MAX_GRID_AREA - (gridSize - 1) * BLOCK_GAP) / gridSize);
}

export interface CodeBlockGridProps {
  /** current grid size (integer after transitions) */
  currentGridSize: number;
  /** 0-1 progress within current transition */
  transitionProgress: number;
  /** previous grid size (for interpolation) */
  previousGridSize: number;
}

const CodeBlockGrid: React.FC<CodeBlockGridProps> = ({
  currentGridSize,
  transitionProgress,
  previousGridSize,
}) => {
  const frame = useCurrentFrame();

  // Compute interpolated block size and assembly opacity
  const { blockPx, opacity } = useMemo(() => {
    const bPx = getBlockSize(currentGridSize);
    const prevBPx = getBlockSize(previousGridSize);
    const interpBlock = prevBPx + (bPx - prevBPx) * transitionProgress;

    // Visible from frame 0, full by frame 20
    const op = interpolate(frame, [0, 20], [0.7, 1], {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
    });

    return { blockPx: interpBlock, opacity: op };
  }, [currentGridSize, previousGridSize, transitionProgress, frame]);

  // Render up to currentGridSize × currentGridSize blocks
  const blocks = useMemo(() => {
    const result: React.ReactNode[] = [];
    const gridN = currentGridSize;
    const bPx = blockPx;
    const totalDim = gridN * bPx + (gridN - 1) * BLOCK_GAP;
    const startX = GRID_CENTER_X - totalDim / 2;
    const startY = GRID_CENTER_Y - totalDim / 2;

    for (let row = 0; row < gridN; row++) {
      for (let col = 0; col < gridN; col++) {
        const idx = row * gridN + col;
        const x = startX + col * (bPx + BLOCK_GAP);
        const y = startY + row * (bPx + BLOCK_GAP);

        // For blocks beyond previous grid size, fade them in during transition
        const wasInPrevious = row < previousGridSize && col < previousGridSize;
        const blockOpacity = wasInPrevious
          ? 1
          : transitionProgress;

        result.push(
          <div
            key={idx}
            style={{
              position: "absolute",
              left: x,
              top: y,
              width: bPx,
              height: bPx,
              backgroundColor: BLOCK_FILL,
              border: `1px solid ${BLOCK_BORDER}`,
              borderRadius: Math.max(1, bPx > 10 ? 3 : 1),
              opacity: blockOpacity,
              transform: `scale(${wasInPrevious ? 1 : 0.95 + 0.05 * transitionProgress})`,
            }}
          />
        );
      }
    }
    return result;
  }, [currentGridSize, previousGridSize, blockPx, transitionProgress]);

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: "100%",
        height: "100%",
        opacity,
      }}
    >
      {blocks}
    </div>
  );
};

export default CodeBlockGrid;
