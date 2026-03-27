import React from "react";
import { AbsoluteFill } from "remotion";
import {
  WIDTH,
  HEIGHT,
  GRID_SPACING,
  GRID_COLOR,
  GRID_OPACITY,
} from "./constants";

export const BlueprintGrid: React.FC = () => {
  const verticalLines: number[] = [];
  for (let x = 0; x <= WIDTH; x += GRID_SPACING) {
    verticalLines.push(x);
  }

  const horizontalLines: number[] = [];
  for (let y = 0; y <= HEIGHT; y += GRID_SPACING) {
    horizontalLines.push(y);
  }

  return (
    <AbsoluteFill style={{ opacity: GRID_OPACITY }}>
      <svg width={WIDTH} height={HEIGHT}>
        {verticalLines.map((x) => (
          <line
            key={`v-${x}`}
            x1={x}
            y1={0}
            x2={x}
            y2={HEIGHT}
            stroke={GRID_COLOR}
            strokeWidth={1}
          />
        ))}
        {horizontalLines.map((y) => (
          <line
            key={`h-${y}`}
            x1={0}
            y1={y}
            x2={WIDTH}
            y2={y}
            stroke={GRID_COLOR}
            strokeWidth={1}
          />
        ))}
      </svg>
    </AbsoluteFill>
  );
};
