import React from "react";
import { AbsoluteFill } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  GRID_SPACING,
  GRID_ACCENT_EVERY,
  GRID_COLOR,
  GRID_BASE_OPACITY,
  GRID_ACCENT_OPACITY,
} from "./constants";

export const BlueprintGrid: React.FC<{ opacity: number }> = ({ opacity }) => {
  const lines: React.ReactNode[] = [];

  // Vertical lines
  for (let x = 0; x <= CANVAS_WIDTH; x += GRID_SPACING) {
    const isAccent = x % GRID_ACCENT_EVERY === 0;
    lines.push(
      <line
        key={`v-${x}`}
        x1={x}
        y1={0}
        x2={x}
        y2={CANVAS_HEIGHT}
        stroke={GRID_COLOR}
        strokeWidth={1}
        opacity={isAccent ? GRID_ACCENT_OPACITY : GRID_BASE_OPACITY}
      />
    );
  }

  // Horizontal lines
  for (let y = 0; y <= CANVAS_HEIGHT; y += GRID_SPACING) {
    const isAccent = y % GRID_ACCENT_EVERY === 0;
    lines.push(
      <line
        key={`h-${y}`}
        x1={0}
        y1={y}
        x2={CANVAS_WIDTH}
        y2={y}
        stroke={GRID_COLOR}
        strokeWidth={1}
        opacity={isAccent ? GRID_ACCENT_OPACITY : GRID_BASE_OPACITY}
      />
    );
  }

  return (
    <AbsoluteFill style={{ opacity }}>
      <svg
        width={CANVAS_WIDTH}
        height={CANVAS_HEIGHT}
        viewBox={`0 0 ${CANVAS_WIDTH} ${CANVAS_HEIGHT}`}
      >
        {lines}
      </svg>
    </AbsoluteFill>
  );
};

export default BlueprintGrid;
