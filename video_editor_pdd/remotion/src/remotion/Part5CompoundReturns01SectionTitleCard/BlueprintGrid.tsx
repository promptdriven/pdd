import React from "react";
import { AbsoluteFill } from "remotion";
import {
  CANVAS_WIDTH,
  CANVAS_HEIGHT,
  GRID_SPACING,
  GRID_COLOR,
  GRID_OPACITY,
} from "./constants";

export const BlueprintGrid: React.FC = () => {
  const verticalLines: number[] = [];
  for (let x = GRID_SPACING; x < CANVAS_WIDTH; x += GRID_SPACING) {
    verticalLines.push(x);
  }
  const horizontalLines: number[] = [];
  for (let y = GRID_SPACING; y < CANVAS_HEIGHT; y += GRID_SPACING) {
    horizontalLines.push(y);
  }

  return (
    <AbsoluteFill>
      <svg
        width={CANVAS_WIDTH}
        height={CANVAS_HEIGHT}
        viewBox={`0 0 ${CANVAS_WIDTH} ${CANVAS_HEIGHT}`}
        style={{ position: "absolute", top: 0, left: 0 }}
      >
        {verticalLines.map((x) => (
          <line
            key={`v-${x}`}
            x1={x}
            y1={0}
            x2={x}
            y2={CANVAS_HEIGHT}
            stroke={GRID_COLOR}
            strokeWidth={1}
            opacity={GRID_OPACITY}
          />
        ))}
        {horizontalLines.map((y) => (
          <line
            key={`h-${y}`}
            x1={0}
            y1={y}
            x2={CANVAS_WIDTH}
            y2={y}
            stroke={GRID_COLOR}
            strokeWidth={1}
            opacity={GRID_OPACITY}
          />
        ))}
      </svg>
    </AbsoluteFill>
  );
};
