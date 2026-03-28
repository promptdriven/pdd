import React from "react";
import { AbsoluteFill, useCurrentFrame, interpolate, Easing } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  GRID_COLS,
  GRID_ROWS,
  GRID_CELL_SIZE,
  GRID_GAP,
  GRID_BASE_OPACITY,
  GRID_CELL_COLOR,
  GRID_GREEN_COLOR,
  GRID_GREEN_INDICES,
} from "./constants";

export const ModuleGrid: React.FC = () => {
  const frame = useCurrentFrame();

  // Grid dims to 0.08 over first 30 frames
  const gridOpacity = interpolate(frame, [0, 30], [0.15, GRID_BASE_OPACITY], {
    extrapolateLeft: "clamp",
    extrapolateRight: "clamp",
    easing: Easing.inOut(Easing.quad),
  });

  const totalWidth = GRID_COLS * (GRID_CELL_SIZE + GRID_GAP) - GRID_GAP;
  const totalHeight = GRID_ROWS * (GRID_CELL_SIZE + GRID_GAP) - GRID_GAP;
  const offsetX = (CANVAS_WIDTH - totalWidth) / 2;
  const offsetY = (CANVAS_HEIGHT - totalHeight) / 2;

  const cells: React.ReactNode[] = [];
  for (let row = 0; row < GRID_ROWS; row++) {
    for (let col = 0; col < GRID_COLS; col++) {
      const index = row * GRID_COLS + col;
      const isGreen = GRID_GREEN_INDICES.includes(index);
      const x = offsetX + col * (GRID_CELL_SIZE + GRID_GAP);
      const y = offsetY + row * (GRID_CELL_SIZE + GRID_GAP);

      cells.push(
        <div
          key={index}
          style={{
            position: "absolute",
            left: x,
            top: y,
            width: GRID_CELL_SIZE,
            height: GRID_CELL_SIZE,
            borderRadius: 4,
            backgroundColor: isGreen ? GRID_GREEN_COLOR : GRID_CELL_COLOR,
            boxShadow: isGreen
              ? `0 0 8px ${GRID_GREEN_COLOR}40`
              : undefined,
          }}
        />
      );
    }
  }

  return (
    <AbsoluteFill style={{ opacity: gridOpacity }}>
      {cells}
    </AbsoluteFill>
  );
};
