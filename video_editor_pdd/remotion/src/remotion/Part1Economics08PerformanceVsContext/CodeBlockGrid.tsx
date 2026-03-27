import React from "react";
import { interpolate, useCurrentFrame, Easing } from "remotion";
import {
  GRID_COLS,
  GRID_ROWS,
  GRID_CELL_SIZE,
  GRID_GAP,
  GRID_CELL_COLOR,
  GRID_CELL_HIGHLIGHT,
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  PHASE_GRID_DIM_START,
  PHASE_GRID_DIM_END,
} from "./constants";

/**
 * A dimmed background grid of code-block-like cells.
 * Dims from full opacity to 30% over PHASE_GRID_DIM frames.
 */
export const CodeBlockGrid: React.FC = () => {
  const frame = useCurrentFrame();

  const gridOpacity = interpolate(
    frame,
    [PHASE_GRID_DIM_START, PHASE_GRID_DIM_END],
    [0.6, 0.3],
    {
      extrapolateLeft: "clamp",
      extrapolateRight: "clamp",
      easing: Easing.out(Easing.quad),
    }
  );

  const totalWidth = GRID_COLS * (GRID_CELL_SIZE + GRID_GAP) - GRID_GAP;
  const totalHeight = GRID_ROWS * (GRID_CELL_SIZE + GRID_GAP) - GRID_GAP;
  const offsetX = (CANVAS_WIDTH - totalWidth) / 2;
  const offsetY = (CANVAS_HEIGHT - totalHeight) / 2;

  const cells: React.ReactNode[] = [];
  for (let row = 0; row < GRID_ROWS; row++) {
    for (let col = 0; col < GRID_COLS; col++) {
      const isHighlight =
        (row + col) % 7 === 0 || (row * 3 + col * 5) % 11 === 0;
      cells.push(
        <div
          key={`${row}-${col}`}
          style={{
            position: "absolute",
            left: offsetX + col * (GRID_CELL_SIZE + GRID_GAP),
            top: offsetY + row * (GRID_CELL_SIZE + GRID_GAP),
            width: GRID_CELL_SIZE,
            height: GRID_CELL_SIZE,
            backgroundColor: isHighlight ? GRID_CELL_HIGHLIGHT : GRID_CELL_COLOR,
            borderRadius: 3,
          }}
        />
      );
    }
  }

  return (
    <div
      style={{
        position: "absolute",
        top: 0,
        left: 0,
        width: CANVAS_WIDTH,
        height: CANVAS_HEIGHT,
        opacity: gridOpacity,
      }}
    >
      {cells}
    </div>
  );
};

export default CodeBlockGrid;
